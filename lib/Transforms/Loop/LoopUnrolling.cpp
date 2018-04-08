#include "llvm/Transforms/Loop/LoopUnrolling.h"

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

#define DEBUG_TYPE "loop-unrolling"

char LoopUnrolling::ID = 0;

static RegisterPass<LoopUnrolling> X("loop-unrolling", "Loop Unrolling Pass", false, false);

LoopUnrolling::LoopUnrolling()
    : FunctionPass(ID) {}

LoopUnrollResult LoopUnrolling::tryToUnrollLoop() {
    return LoopUnrollResult::Unmodified;
}

bool LoopUnrolling::runOnFunction(Function& function) {
    auto& loopInfo = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
    auto& dominatorTree = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
    auto& scalarEvolution = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
    auto& assumptionCache = getAnalysis<AssumptionCacheTracker>().getAssumptionCache(function);
    OptimizationRemarkEmitter optimizationRemarkEmitter {&function};

    return false;
}

void LoopUnrolling::getAnalysisUsage(AnalysisUsage& analysisUsage) const {
    analysisUsage.addRequired<LoopInfoWrapperPass>();
    analysisUsage.addRequired<DominatorTreeWrapperPass>();
    analysisUsage.addRequired<ScalarEvolutionWrapperPass>();
    analysisUsage.addRequired<AssumptionCacheTracker>();
    analysisUsage.setPreservesAll();
}
