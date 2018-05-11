#include "llvm/Transforms/Loop/SLPAwareLoopUnroll.h"

#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/Analysis/LoopUnrollAnalyzer.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"

using namespace llvm;

#define DEBUG_TYPE "slp-aware-loop-unroll"

char SLPAwareLoopUnrollPass::ID = 0;

static RegisterPass<SLPAwareLoopUnrollPass> X("slp-aware-loop-unroll", "Loop Unrolling Pass", false, false);

namespace {
std::string toString(const LoopUnrollResult& LUR) {
  switch (LUR) {
    case LoopUnrollResult::FullyUnrolled: return "FullyUnrolled";
    case LoopUnrollResult::PartiallyUnrolled: return "PartiallyUnrolled";
    case LoopUnrollResult::Unmodified: return "Unmodified";
  }
  return {};
}
}

unsigned getSmallestStoreSize(const StoreList& SL, unsigned MaxSize) {
  dbgs() << "SALU: Stors sizes\n";
  for (auto * SI : SL) {
    unsigned Size = SI->getValueOperand()->getType()->getScalarSizeInBits();
    dbgs() << "\t" << Size << "\n";
    if (Size < MaxSize)
      MaxSize = Size;
  }
  return MaxSize;
}

void fetchStoreInstructions(BasicBlock* BB, StoreList& SL)
{
  for (auto &I : *BB)
    if (auto *SI = dyn_cast<StoreInst>(&I))
      if (SI->isSimple())
        SL.push_back(SI);
}

unsigned getOptimalUnrollCount(const Loop& L, const TargetTransformInfo& TTI)
{
  unsigned MaxVecRegSize = TTI.getRegisterBitWidth(true);
  unsigned MinVecRegSize = TTI.getMinVectorRegisterBitWidth();
  dbgs() << "SALU: MaxVecRegSize " << MaxVecRegSize
         << " MinVecRegSize " << MinVecRegSize << "\n";

  StoreList SL;
  for (auto BB : L.getBlocks())
    fetchStoreInstructions(BB, SL);

  unsigned SmallestStoreSize = getSmallestStoreSize(SL, MaxVecRegSize);

  return MaxVecRegSize/SmallestStoreSize;
}

LoopUnrollResult tryToUnrollLoop(unsigned Count, Loop &L, LoopInfo &LI,
                                 ScalarEvolution &SE, DominatorTree &DT,
                                 AssumptionCache &AC,
                                 OptimizationRemarkEmitter &ORE) {

  if (!L.isLoopSimplifyForm()) {
      dbgs() << "SALU: Loop is not on a simplified form.\n";
      return LoopUnrollResult::Unmodified;
  }

  unsigned TripCount = 0;
  unsigned TripMultiple = 1;

  auto* ExitingBlock = L.getLoopLatch();
  if (!ExitingBlock || !L.isLoopExiting(ExitingBlock)) {
    dbgs() << "SALU: Has no latch or latch is not an exiting block.\n";
    ExitingBlock = L.getExitingBlock();
  }

  if (ExitingBlock) {
    dbgs() << "SALU: Has exiting block.\n";
    TripCount = SE.getSmallConstantTripCount(&L, ExitingBlock);
    TripMultiple = SE.getSmallConstantTripMultiple(&L, ExitingBlock);
  }

  if (!TripCount) {
    dbgs() << "SALU: Could not find a TripCount for this Loop.\n";
    return LoopUnrollResult::Unmodified;
  }

  if (Count > TripCount) {
    dbgs() << "SALU: TripCount is less than Count.\n";
    Count = TripCount;
  }

  auto Result = UnrollLoop(&L, Count, TripCount, true, true, true, false, false,
                           TripMultiple, 0, false, &LI, &SE, &DT, &AC, &ORE,
                           true);

  dbgs() << "SALU: Unroll Loop metrics:\n"
         << "\tCount: " << Count << "\n"
         << "\tTripCount: " << TripCount << "\n"
         << "\tTripMultiple: " << TripMultiple << "\n"
         << "\tLoopUnrollResult: " << toString(Result) << "\n";

  if (Result == LoopUnrollResult::PartiallyUnrolled)
    L.setLoopAlreadyUnrolled();

  return Result;
}

bool SLPAwareLoopUnrollPass::runImpl(Function &F, LoopInfo &LI,
                                     ScalarEvolution &SE, DominatorTree &DT,
                                     AssumptionCache &AC,
                                     TargetTransformInfo &TTI,
                                     OptimizationRemarkEmitter &ORE) {

  if (!TTI.getNumberOfRegisters(true))
    return false;

  bool Changed = false;


  for (auto BB : post_order(&F.getEntryBlock())) {
      auto* L = LI.getLoopFor(BB);

      if (L && L->getSubLoops().empty()) {
        dbgs() << "Loop: " << *L << "\n";
        unsigned Count = getOptimalUnrollCount(*L, TTI);
        auto Result = tryToUnrollLoop(Count, *L, LI, SE, DT, AC, ORE);

        Changed |= Result != LoopUnrollResult::Unmodified;
      }
  }
  return Changed;
}

SLPAwareLoopUnrollPass::SLPAwareLoopUnrollPass() : FunctionPass(ID) {}

bool SLPAwareLoopUnrollPass::runOnFunction(Function& F) {
    auto &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
    auto &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
    auto &SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
    auto &AC = getAnalysis<AssumptionCacheTracker>().getAssumptionCache(F);
    auto &TTI = getAnalysis<TargetTransformInfoWrapperPass>().getTTI(F);
    OptimizationRemarkEmitter ORE {&F};

    return runImpl(F, LI, SE, DT, AC, TTI, ORE);
}

void SLPAwareLoopUnrollPass::getAnalysisUsage(AnalysisUsage& AU) const {
    AU.addRequired<LoopInfoWrapperPass>();
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.addRequired<ScalarEvolutionWrapperPass>();
    AU.addRequired<AssumptionCacheTracker>();
    AU.addRequired<TargetTransformInfoWrapperPass>();
    AU.setPreservesAll();
}
