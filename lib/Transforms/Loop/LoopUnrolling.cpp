#include "llvm/Transforms/Loop/LoopUnrolling.h"

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

#define DEBUG_TYPE "loop-unrolling"

char LoopUnrolling::ID = 0;

static RegisterPass<LoopUnrolling> X("loop-unrolling", "Loop Unrolling Pass", false, false);

namespace
{
    std::string toString(const LoopUnrollResult& loopUnrollResult)
    {
        switch (loopUnrollResult)
        {
            case LoopUnrollResult::FullyUnrolled: return "FullyUnrolled";
            case LoopUnrollResult::PartiallyUnrolled: return "PartiallyUnrolled";
            case LoopUnrollResult::Unmodified: return "Unmodified";
        }
        return {};
    }
}

LoopUnrolling::LoopUnrolling()
    : FunctionPass(ID) {}

std::vector<Loop*> LoopUnrolling::getLeafLoops(Loop& rootLoop)
{
    std::vector<Loop*> leafLoops;
    std::vector<Loop*> stackLoops;

    stackLoops.push_back(&rootLoop);
    while(!stackLoops.empty())
    {
        auto* loop = stackLoops.back();
        if (loop->getSubLoops().empty())
        {
            leafLoops.push_back(loop);
        }
        else
        {
            for (auto* leafLoop : loop->getSubLoops())
            {
                stackLoops.push_back(leafLoop);
            }
        }
        stackLoops.pop_back();
    }

    return leafLoops;
}

LoopUnrollResult LoopUnrolling::tryToUnrollLoop(unsigned                   count,
                                                Loop&                      loop,
                                                LoopInfo&                  loopInfo,
                                                ScalarEvolution&           scalarEvolution,
                                                DominatorTree&             dominatorTree,
                                                AssumptionCache&           assumptionCache,
                                                OptimizationRemarkEmitter& optimizationRemarkEmitter) {

    if (!loop.isLoopSimplifyForm())
    {
        dbgs() << "Loop is not on a simplified form.\n";
        return LoopUnrollResult::Unmodified;
    }

    unsigned tripCount = 0;
    unsigned tripMultiple = 1;

    auto* exitingBlock = loop.getLoopLatch();
    if (!exitingBlock || !loop.isLoopExiting(exitingBlock))
    {
        dbgs() << "Has no latch or latch is not an exiting block.\n";
        exitingBlock = loop.getExitingBlock();
    }

    if (exitingBlock)
    {
        dbgs() << "Has exiting block.\n";
        tripCount = scalarEvolution.getSmallConstantTripCount(&loop, exitingBlock);
        tripMultiple = scalarEvolution.getSmallConstantTripMultiple(&loop, exitingBlock);
    }

    if (!tripCount)
    {
        dbgs() << "Could not find a tripCount for this Loop.\n";
        return LoopUnrollResult::Unmodified;
    }

    if (count > tripCount)
    {
        dbgs() << "tripCount is lass than count.\n";
        count = tripCount;
    }

    auto result = UnrollLoop(&loop,
                             count,
                             tripCount,
                             /*force*/ true,
                             /*allowRuntime*/ true,
                             /*allowExpensiveTripCount*/ true,
                             /*preserveCondBr*/ false,
                             /*preserveOnlyFirst*/ false,
                             tripMultiple,
                             /*peelCount*/ 0,
                             /*unrollRemainder*/ false,
                             &loopInfo,
                             &scalarEvolution,
                             &dominatorTree,
                             &assumptionCache,
                             &optimizationRemarkEmitter,
                             /*preserveLCSSA*/ true);

    dbgs() << "\ncount: " << count
           << "\ntripCount: " << tripCount
           << "\ntripMultiple: " << tripMultiple
           << "\n";

    if (result == LoopUnrollResult::PartiallyUnrolled)
    {
        loop.setLoopAlreadyUnrolled();
    }

    dbgs() << "LoopUnrollResult: " << toString(result) << "\n";

    return result;
}

bool LoopUnrolling::runOnFunction(Function& function)
{
    auto& loopInfo = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
    auto& dominatorTree = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
    auto& scalarEvolution = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
    auto& assumptionCache = getAnalysis<AssumptionCacheTracker>().getAssumptionCache(function);
    OptimizationRemarkEmitter optimizationRemarkEmitter {&function};

    bool modified = false;
    for (auto basicBlock : post_order(&function.getEntryBlock()))
    {
        auto* loop = loopInfo.getLoopFor(basicBlock);
        if (loop && loop->getSubLoops().empty())
        {
            auto loopUnrollResult = tryToUnrollLoop(/*count*/ 4,
                                                    *loop,
                                                    loopInfo,
                                                    scalarEvolution,
                                                    dominatorTree,
                                                    assumptionCache,
                                                    optimizationRemarkEmitter);

            if (loopUnrollResult != LoopUnrollResult::Unmodified)
            {
                modified = true;
            }
        }
    }
    return modified;
}

void LoopUnrolling::getAnalysisUsage(AnalysisUsage& analysisUsage) const
{
    analysisUsage.addRequired<LoopInfoWrapperPass>();
    analysisUsage.addRequired<DominatorTreeWrapperPass>();
    analysisUsage.addRequired<ScalarEvolutionWrapperPass>();
    analysisUsage.addRequired<AssumptionCacheTracker>();
    analysisUsage.setPreservesAll();
}
