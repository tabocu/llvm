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

int costTree(const StoreInst *SI, const Loop &L) {
  int cost = 0;
  SmallVector<const Value*, 16> ValStack;
  ValStack.push_back(SI->getValueOperand());
  dbgs() << "SALU: Building CostTree...\n";
  dbgs() << "\t" << *SI << "\n";
  dbgs() << "\t\tInitial Store instruction\n";
  while (!ValStack.empty()) {
    const auto *Val = ValStack.back();
    ValStack.pop_back();
    dbgs() << "\t" << *Val << "\n";

    const auto *Inst = dyn_cast<Instruction>(Val)

    if (Inst && L.contains(Inst)) {
      if (L.isLoopInvariant(Inst)) {
        // Compute the cost for insert instr and stop exploring this branch
      } else {
        switch (Inst->getOpcode()) {
          case Instruction::Load: {
            dbgs() << "\t\tFound Load instruction\n";
            continue;
          }
          default: {
            dbgs() << "\t\tUnknown instruction\n";
            break;
          }
        }
      }
    } else {
      dbgs() << "\t\tIt isn't an instruction\n";
      // Compute the cost for insert instr and stop exploring this branch
    }

    if (L.isLoopInvariant(Val)) {
      dbgs() << "\t\tFound Loop Invariant instruction\n";
    } else {
      const auto *U = dyn_cast<User>(Val);
      std::copy(U->op_begin(), U->op_end(),
                std::back_inserter(ValStack));
    }
  }
  return cost;
}

bool isLoopInvariantSVEC(const SCEV *VarSCEV, const Loop &L) {
  SmallVector<const SCEV*, 16> OpSCEVStack;
  OpSCEVStack.push_back(VarSCEV);

  dbgs() << "SALU: Checking for loop invariant SCEV...\n";
  while (!OpSCEVStack.empty()) {
    const auto *OpSCEV = OpSCEVStack.back();
    OpSCEVStack.pop_back();

    dbgs() << "\t" << *OpSCEV << "\n";
    if (auto *CommSCEV = dyn_cast<SCEVCommutativeExpr>(OpSCEV)) {
      dbgs() << "\tSCEVCommutativeExpr\n";
      std::copy(CommSCEV->op_begin(), CommSCEV->op_end(),
                std::back_inserter(OpSCEVStack));
    } else if (auto *CastSCEV = dyn_cast<SCEVCastExpr>(OpSCEV)) {
      dbgs() << "\tSCEVCastExpr\n";
      OpSCEVStack.push_back(CastSCEV->getOperand());
    } else if (auto *UnkSCEV = dyn_cast<SCEVUnknown>(OpSCEV)) {
      dbgs() << "\tSCEVUnknown\n";
      if (!L.isLoopInvariant(UnkSCEV->getValue())) {
        dbgs() << "\t\tIt isn't Loop Invariant\n";
        return false;
      }
    } else if (isa<SCEVConstant>(OpSCEV)) {
      dbgs() << "\tSCEVConstant\n";
    } else {
      dbgs() << "\tInvalid SCEV\n";
      return false;
    }
  }
  return true;
}

const SCEVAddRecExpr* unpackAddRecExprSCEV(const SCEV *VarSCEV, const Loop &L) {
  SmallVector<const SCEV*, 16> OpSCEVStack;
  OpSCEVStack.push_back(VarSCEV);

  dbgs() << "SALU: Unpacking AddRecExpr SCEV...\n";
  const SCEVAddRecExpr *AddRecSCEV {nullptr};
  while (!OpSCEVStack.empty()) {
    const auto *OpSCEV = OpSCEVStack.back();
    OpSCEVStack.pop_back();

    dbgs() << "\t" << *OpSCEV << "\n";
    if (auto *CommSCEV = dyn_cast<SCEVCommutativeExpr>(OpSCEV)) {
      dbgs() << "\tSCEVCommutativeExpr\n";
      if (isa<SCEVAddExpr>(CommSCEV)) {
        dbgs() << "\t\tSCEVAddExpr\n";
        std::copy(CommSCEV->op_begin(), CommSCEV->op_end(),
                  std::back_inserter(OpSCEVStack));
      } else if(!isLoopInvariantSVEC(OpSCEV, L)) {
        dbgs() << "It isn't Loop Invariant SCEV\n";
        return nullptr;
      }
    } else if (auto *CastSCEV = dyn_cast<SCEVCastExpr>(OpSCEV)) {
      dbgs() << "\tSCEVCastExpr\n";
      OpSCEVStack.push_back(CastSCEV->getOperand());
    } else if (auto *UnkSCEV = dyn_cast<SCEVUnknown>(OpSCEV)) {
      dbgs() << "\tSCEVUnknown\n";
      if (!L.isLoopInvariant(UnkSCEV->getValue())) {
        dbgs() << "\t\tIt isn't Loop Invariant\n";
        return nullptr;
      }
    } else if (isa<SCEVAddRecExpr>(OpSCEV)) {
      dbgs() << "\tSCEVAddRecExpr\n";
      if (AddRecSCEV) {
        dbgs() << "\t\tMultiple AddRecSCEV's\n";
        return nullptr;
      }
      AddRecSCEV = dyn_cast<const SCEVAddRecExpr>(OpSCEV);
    } else if (isa<SCEVConstant>(OpSCEV)) {
      dbgs() << "\tSCEVConstant\n";
    } else {
      dbgs() << "\tInvalid SCEV\n";
      return nullptr;
    }
  }
  return AddRecSCEV;
}

bool isSuitableSCEV(const SCEV *RecSCEV, const Loop &L) {
  if (auto *AddRecSCEV = unpackAddRecExprSCEV(RecSCEV, L)) {
    dbgs() << "SALU: SCEV is an AddRecExpr\n";

    if (AddRecSCEV->getLoop() != &L) {
      dbgs() << "SALU: Doesnt belong to current Loop\n";
      return false;
    }

    if (!AddRecSCEV->getOperand(1)->isOne()) {
      dbgs() << "SALU: Increment operand is not zero\n";
      return false;
    }

    dbgs() << "SALU: SCEV is suitable\n";
    return true;
  }

  dbgs() << "SALU: SCEV is not an AddRecExpr\n";
  return false;
}

bool isSuitableLoadStoreInst(ScalarEvolution &SE, Loop &L, Instruction &I) {
  const GetElementPtrInst* GEPI = nullptr;
  dbgs() << "\nSALU: Checking for suitable load or store instructions\n";
  if (auto *SI = dyn_cast<StoreInst>(&I)) {
    dbgs() << "SALU: " << *SI << "\n";
    if (SI->isSimple())
      GEPI = dyn_cast<GetElementPtrInst>(SI->getPointerOperand());
  } else if (auto *LI = dyn_cast<LoadInst>(&I)) {
    dbgs() << "SALU: " << *LI << "\n";
    if (LI->isSimple())
      GEPI = dyn_cast<GetElementPtrInst>(LI->getPointerOperand());
  }

  if (GEPI) {
    const auto *OP1 = dyn_cast<ConstantInt>(GEPI->getOperand(1));
    auto *OP2 = GEPI->getOperand(2);
    if (OP1 && OP1->isZero()) return isSuitableSCEV(SE.getSCEV(OP2), L);
  }

  return false;
}

unsigned getSmallestStoreSize(const StoreList& SL, unsigned MaxSize) {
  dbgs() << "SALU: Stors sizes\n";
  for (auto * SI : SL) {
    // TODO: SPL has a more suitable way to get size.
    // getVectorElementSize(Value *V) on line 3826
    unsigned Size = SI->getValueOperand()->getType()->getScalarSizeInBits();
    dbgs() << "\t" << Size << "\n";
    if (Size < MaxSize)
      MaxSize = Size;
  }
  return MaxSize;
}

template <class C>
bool isStoreOrLoadIndexedByLoop(const Loop &L, const Instruction &I) {
  if (auto *CI = dyn_cast<C>(&I))
    if (CI->isSimple())
      if (auto *GEPI = dyn_cast<GetElementPtrInst>(CI->getPointerOperand()))
        return GEPI->getOperand(2) == L.getCanonicalInductionVariable();
  return false;
}

StoreList fetchStoreInst(Loop &L) {
  StoreList SL;

  for (auto *BB : L.getBlocks())
    for (auto &I : *BB)
      if (isStoreOrLoadIndexedByLoop<StoreInst>(L, I))
        dbgs() << "ACHOU\n";

  return SL;
}

void fetchStoreInstructions(BasicBlock* BB, StoreList& SL) {
  for (auto &I : *BB)
    if (auto *SI = dyn_cast<StoreInst>(&I))
      if (SI->isSimple())
        SL.push_back(SI);
}

unsigned getOptimalUnrollCount(const Loop& L, const TargetTransformInfo& TTI) {
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

  if (!TTI.getNumberOfRegisters(true)) return false;

  bool Changed = false;

  for (auto BB : post_order(&F.getEntryBlock())) {
      auto* L = LI.getLoopFor(BB);
      if (L && L->getSubLoops().empty())
        for (auto *BB : L->getBlocks())
          for (auto &I : *BB)
          {
//            isSuitableLoadStoreInst(SE, *L, I);
            if (const auto *SI = dyn_cast<StoreInst>(&I))
              costTree(SI, *L);
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
