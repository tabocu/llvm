#include "llvm/Transforms/Loop/SLPAwareLoopUnroll.h"

#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/VectorUtils.h"
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

// ----------------------------------------------

Type *getScalarType(Value *V) {
  if (auto *SI = dyn_cast<StoreInst>(V))
    return SI->getValueOperand()->getType();
  else if (auto *CI = dyn_cast<CmpInst>(V))
    return CI->getOperand(0)->getType();
  else
    return V->getType();
}

int getCastCost(TargetTransformInfo *TTI,
                Value *V,
                Type *ScaTy,
                unsigned W) {

  auto *I = cast<Instruction>(V);

  Type *SrcScaTy = I->getOperand(0)->getType();
  VectorType *VecTy = VectorType::get(ScaTy, W);
  VectorType *SrcVecTy = VectorType::get(SrcScaTy, W);

  int ScaCost = W*TTI->getCastInstrCost(I->getOpcode(),
                                        I->getType(),
                                        SrcScaTy,
                                        I);

  int VecCost = TTI->getCastInstrCost(I->getOpcode(),
                                      VecTy,
                                      SrcVecTy,
                                      I);
  return VecCost - ScaCost;
}

int getCmpSelCost(TargetTransformInfo *TTI,
                  IRBuilder<> &Builder,
                  Value *V,
                  Type *ScaTy,
                  unsigned W) {
  auto *I = cast<Instruction>(V);

  Type *Int1ScaTy = Builder.getInt1Ty(); // TODO: Solve builder

  VectorType *VecTy = VectorType::get(ScaTy, W);
  VectorType *Int1VecTy = VectorType::get(Int1ScaTy, W);

  unsigned N = VecTy->getNumElements();

  int ScaCost = N*TTI->getCmpSelInstrCost(I->getOpcode(),
                                          ScaTy,
                                          Int1ScaTy,
                                          I);

  int VecCost = TTI->getCmpSelInstrCost(I->getOpcode(),
                                        VecTy,
                                        Int1VecTy,
                                        I);

  return VecCost - ScaCost;
}

using OpVK = TargetTransformInfo::OperandValueKind;
using OpVP = TargetTransformInfo::OperandValueProperties;

int getArithmeticCost(TargetTransformInfo *TTI,
                      Value *V,
                      Type *ScaTy,
                      unsigned W) {
  auto *I = cast<Instruction>(V);

  VectorType *VecTy = VectorType::get(ScaTy, W);

  unsigned N = VecTy->getNumElements();

  OpVK Op1VK = TargetTransformInfo::OK_AnyValue;
  OpVP Op1VP = TargetTransformInfo::OP_None;

  OpVK Op2VK = TargetTransformInfo::OK_UniformConstantValue;
  OpVP Op2VP = TargetTransformInfo::OP_None;

  // If all operands are exactly the same ConstantInt then set the
  // operand kind to OK_UniformConstantValue.
  // If instead not all operands are constants, then set the operand kind
  // to OK_AnyValue. If all operands are constants but not the same,
  // then set the operand kind to OK_NonUniformConstantValue.
  if (ConstantInt *CInt = dyn_cast<ConstantInt>(I->getOperand(1))) {
    if (Op2VK == TargetTransformInfo::OK_UniformConstantValue &&
          CInt->getValue().isPowerOf2()) {
      Op2VP = TargetTransformInfo::OP_PowerOf2;
    }
  } else {
    Op2VK = TargetTransformInfo::OK_AnyValue;
  }

  SmallVector<const Value *, 4> Operands(I->operand_values());

  int ScaCost = N*TTI->getArithmeticInstrCost(I->getOpcode(),
                                              ScaTy,
                                              Op1VK,
                                              Op2VK,
                                              Op1VP,
                                              Op2VP,
                                              Operands);

  int VecCost = TTI->getArithmeticInstrCost(I->getOpcode(),
                                            VecTy,
                                            Op1VK,
                                            Op2VK,
                                            Op1VP,
                                            Op2VP,
                                            Operands);

  return VecCost - ScaCost;
}

int getMemoryCost(TargetTransformInfo *TTI,
                  Value *V,
                  Type *ScaTy,
                  unsigned W) {
  auto *I = cast<Instruction>(V);

  VectorType *VecTy = VectorType::get(ScaTy, W);

  unsigned N = VecTy->getNumElements();

  unsigned alignment = 0;
  if (auto *LI = dyn_cast<LoadInst>(I)) {
    alignment = LI->getAlignment();
  } else if (auto *SI = dyn_cast<StoreInst>(I)) {
    alignment = SI->getAlignment();
  } else {
    assert(0 && "Neither a Load or Store instruction");
  }

  int ScaCost = N*TTI->getMemoryOpCost(I->getOpcode(),
                                       ScaTy,
                                       alignment,
                                       0,
                                       I);

  int VecCost = TTI->getMemoryOpCost(I->getOpcode(),
                                     VecTy,
                                     alignment,
                                     0,
                                     I);

  return VecCost - ScaCost;
}

int getCallCost(TargetTransformInfo *TTI,
                TargetLibraryInfo *TLI,
                Value *V,
                Type *ScaTy,
                unsigned W) {

  auto *I = cast<Instruction>(V);

  VectorType *VecTy = VectorType::get(ScaTy, W);

  unsigned N = VecTy->getNumElements();

  CallInst *CI = cast<CallInst>(I);
  Intrinsic::ID ID = getVectorIntrinsicIDForCall(CI, TLI);

  // Calculate the cost of the scalar and vector calls.
  SmallVector<Type*, 4> ScaTys;
  for (unsigned op = 0, opc = CI->getNumArgOperands(); op != opc; ++op) {
    ScaTys.push_back(CI->getArgOperand(op)->getType());
  }

  FastMathFlags FMF;
  if (auto *FPMO = dyn_cast<FPMathOperator>(CI)) {
    FMF = FPMO->getFastMathFlags();
  }

  int ScaCost = W*TTI->getIntrinsicInstrCost(ID,
                                             ScaTy,
                                             ScaTys,
                                             FMF);

  SmallVector<Value *, 4> Args(CI->arg_operands());
  int VecCost = TTI->getIntrinsicInstrCost(ID,
                                           CI->getType(),
                                           Args,
                                           FMF,
                                           N);

  return VecCost - ScaCost;
}

int getElementPtrCost(const TargetTransformInfo *TTI,
                      const Value *V,
                      Type *ScaTy,
                      unsigned W) {

  VectorType *VecTy = VectorType::get(ScaTy, W);

  unsigned N = VecTy->getNumElements();

  OpVK Op1VK = TargetTransformInfo::OK_AnyValue;
  OpVK Op2VK = TargetTransformInfo::OK_UniformConstantValue;

  int ScaCost = N*TTI->getArithmeticInstrCost(Instruction::Add,
                                              ScaTy,
                                              Op1VK,
                                              Op2VK);

  int VecCost = TTI->getArithmeticInstrCost(Instruction::Add,
                                            VecTy,
                                            Op1VK,
                                            Op2VK);

  return VecCost - ScaCost;
}

int getShuffleVector(TargetTransformInfo *TTI,
                     Value *V,
                     Type *ScaTy,
                     unsigned W) {

  auto *I = cast<Instruction>(V);

  VectorType *VecTy = VectorType::get(ScaTy, W);

  OpVK Op1VK = TargetTransformInfo::OK_AnyValue;
  OpVK Op2VK = TargetTransformInfo::OK_AnyValue;

  int ScaCost = W*TTI->getArithmeticInstrCost(I->getOpcode(),
                                              ScaTy,
                                              Op1VK,
                                              Op2VK);

  // VecCost is equal to sum of the cost of creating 2 vectors
  // and the cost of creating shuffle.
  int VecCost = 2*TTI->getArithmeticInstrCost(I->getOpcode(),
                                              VecTy,
                                              Op1VK,
                                              Op2VK);

  VecCost += TTI->getShuffleCost(TargetTransformInfo::SK_Alternate,
                                 VecTy,
                                 0);

  return VecCost - ScaCost;
}

int getExtractCost(TargetTransformInfo *TTI,
                   Value *V,
                   Type *ScaTy,
                   unsigned W) {
  VectorType *VecTy = VectorType::get(ScaTy, W);

  unsigned N = VecTy->getNumElements();

  int Cost = 0;
  for (unsigned i = 0; i < N; ++i) {
    Cost += TTI->getVectorInstrCost(Instruction::InsertElement, VecTy, i);
  }
  return Cost;
}

int SLPAwareLoopUnrollPass::getEntryCost(TargetTransformInfo *TTI,
                                         TargetLibraryInfo *TLI,
                                         IRBuilder<> &Builder,
                                         Value *V,
                                         unsigned W) {
  Type *ScaTy = getScalarType(V);

  if (!ScaTy || !PointerType::isValidElementType(ScaTy)) {
    return 0;
  }

  unsigned OpCode = cast<Instruction>(V)->getOpcode();

  assert(OpCode && "Invalid V");

  switch (OpCode) {
    case Instruction::PHI:
      return 0;
    case Instruction::ExtractValue:
    case Instruction::ExtractElement:
      return getExtractCost(TTI, V, ScaTy, W);

    case Instruction::ZExt:
    case Instruction::SExt:
    case Instruction::FPToUI:
    case Instruction::FPToSI:
    case Instruction::FPExt:
    case Instruction::PtrToInt:
    case Instruction::IntToPtr:
    case Instruction::SIToFP:
    case Instruction::UIToFP:
    case Instruction::Trunc:
    case Instruction::FPTrunc:
    case Instruction::BitCast:
      return getCastCost(TTI, V, ScaTy, W);

    case Instruction::FCmp:
    case Instruction::ICmp:
    case Instruction::Select:
      return getCmpSelCost(TTI, Builder, V, ScaTy, W);

    case Instruction::Add:
    case Instruction::FAdd:
    case Instruction::Sub:
    case Instruction::FSub:
    case Instruction::Mul:
    case Instruction::FMul:
    case Instruction::UDiv:
    case Instruction::SDiv:
    case Instruction::FDiv:
    case Instruction::URem:
    case Instruction::SRem:
    case Instruction::FRem:
    case Instruction::Shl:
    case Instruction::LShr:
    case Instruction::AShr:
    case Instruction::And:
    case Instruction::Or:
    case Instruction::Xor:
      return getArithmeticCost(TTI, V, ScaTy, W);

    case Instruction::GetElementPtr:
      return getElementPtrCost(TTI, V, ScaTy, W);

    case Instruction::Load:
    case Instruction::Store:
      return getMemoryCost(TTI, V, ScaTy, W);

    case Instruction::Call:
      return getCallCost(TTI, TLI, V, ScaTy, W);

    case Instruction::ShuffleVector:
      return getShuffleVector(TTI, V, ScaTy, W);

    default:
      llvm_unreachable("Unknown instruction");
  }
}

int SLPAwareLoopUnrollPass::costTree(TargetTransformInfo *TTI,
                                     TargetLibraryInfo *TLI,
                                     IRBuilder<> &Builder,
                                     Loop *L,
                                     StoreInst *SI,
                                     unsigned W) {
  int cost = 0;
  SmallVector<Value*, 16> ValStack;
  ValStack.push_back(SI->getValueOperand());
  while (!ValStack.empty()) {
    auto *V = ValStack.back();
    ValStack.pop_back();

    auto *I = dyn_cast<Instruction>(V);

    if (I && L->contains(I) && !L->isLoopInvariant(I)) {
       switch (I->getOpcode()) {
         case Instruction::Load: {
           dbgs() << "\t\tFound Load instruction\n";
           continue;
         }
         default: {
           dbgs() << "\t\tUnknown instruction\n";
           break;
         }
       }
    } else {
      dbgs() << "\t\tIt isn't an instruction\n";
      cost += getEntryCost(TTI, TLI, Builder, V, W);
    }

    if (L->isLoopInvariant(V)) {
      dbgs() << "\t\tFound Loop Invariant instruction\n";
    } else {
      auto *U = dyn_cast<User>(V);
      std::copy(U->op_begin(), U->op_end(),
                std::back_inserter(ValStack));
    }
  }
  return cost;
}

bool SLPAwareLoopUnrollPass::runImpl(Function &F,
                                     LoopInfo *LI,
                                     ScalarEvolution *SE,
                                     DominatorTree *DT,
                                     AssumptionCache *AC,
                                     TargetTransformInfo *TTI,
                                     OptimizationRemarkEmitter *ORE,
                                     TargetLibraryInfo *TLI,
                                     IRBuilder<>& Builder) {

  if (!TTI->getNumberOfRegisters(true)) return false;

  bool Changed = false;

  for (auto BB : post_order(&F.getEntryBlock())) {
    auto* L = LI->getLoopFor(BB);
    if (L && L->getSubLoops().empty()) {
      for (auto *BB : L->getBlocks()) {
        for (auto &I : *BB) {
          dbgs() << I << " - " << getEntryCost(TTI, TLI, Builder, &I, 4) << "\n";
        }
      }
    }
  }
  return Changed;
}

SLPAwareLoopUnrollPass::SLPAwareLoopUnrollPass() : FunctionPass(ID) {}

bool SLPAwareLoopUnrollPass::runOnFunction(Function& F) {
    auto *LI = &getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
    auto *DT = &getAnalysis<DominatorTreeWrapperPass>().getDomTree();
    auto *SE = &getAnalysis<ScalarEvolutionWrapperPass>().getSE();
    auto *AC = &getAnalysis<AssumptionCacheTracker>().getAssumptionCache(F);
    auto *TTI = &getAnalysis<TargetTransformInfoWrapperPass>().getTTI(F);
    auto *ORE = &getAnalysis<OptimizationRemarkEmitterWrapperPass>().getORE();
    auto *TLIP = getAnalysisIfAvailable<TargetLibraryInfoWrapperPass>();
    auto *TLI = TLIP ? &TLIP->getTLI() : nullptr;
    IRBuilder<> Builder(SE->getContext());

    return runImpl(F, LI, SE, DT, AC, TTI, ORE, TLI, Builder);
}

void SLPAwareLoopUnrollPass::getAnalysisUsage(AnalysisUsage& AU) const {
    FunctionPass::getAnalysisUsage(AU);
    AU.addRequired<LoopInfoWrapperPass>();
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.addRequired<ScalarEvolutionWrapperPass>();
    AU.addRequired<AssumptionCacheTracker>();
    AU.addRequired<TargetTransformInfoWrapperPass>();
    AU.addRequired<OptimizationRemarkEmitterWrapperPass>();
    AU.setPreservesAll();
}
