// This file is part of llvm2KITTeL
//
// Copyright 2010-2014 Stephan Falke
//
// Licensed under the University of Illinois/NCSA Open Source License.
// See LICENSE for details.

#include "llvm2kittel/Converter.h"
#include "llvm2kittel/IntTRS/Polynomial.h"
#include "llvm2kittel/IntTRS/Rule.h"
#include "llvm2kittel/IntTRS/Term.h"
#include "llvm2kittel/Util/Version.h"

//<Negar>
#include <llvm/Support/raw_ostream.h>
//</Negar>

// llvm includes
#include "WARN_OFF.h"
#if LLVM_VERSION < VERSION(3, 3)
#include <llvm/Constants.h>
#else
#include <llvm/IR/Constants.h>
#endif
#include <llvm/ADT/SmallVector.h>
#if LLVM_VERSION < VERSION(3, 5)
#include <llvm/Support/CallSite.h>
#else
#include <llvm/IR/CallSite.h>
#endif
#if LLVM_VERSION < VERSION(3, 4)
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#else
#include <llvm/Analysis/CFG.h>
#endif
#include "WARN_ON.h"

// C++ includes
#include <iostream>
#include <sstream>
#include <fstream>
#include <vector>
#include <cstdlib>

#define SMALL_VECTOR_SIZE 8

//<Negar>
//Converter::Converter(const llvm::Type *boolType, bool assumeIsControl, bool selectIsControl, bool onlyMultiPredIsControl, bool boundedIntegers, bool unsignedEncoding, bool onlyLoopConditions, DivRemConstraintType divisionConstraintType, bool bitwiseConditions, bool complexityTuples, const bool t2Output)
//        : m_entryBlock(NULL),
//          m_boolType(boolType),
//          m_blockRules(),
//          m_rules(),
//          m_vars(),
//          m_lhs(),
//          m_counter(0),
//          m_phase1(true),
//          m_globals(),
//          m_mmMap(),
//          m_funcMayZap(),
//          m_tfMap(),
//          m_elcMap(),
//          m_returns(),
//          m_idMap(),
//          m_phiMap(),
//          m_nondef(0),
//          m_assumeIsControl(assumeIsControl),
//          m_selectIsControl(selectIsControl),
//          m_onlyMultiPredIsControl(onlyMultiPredIsControl),
//          m_controlPoints(),
//          m_trivial(false),
//          m_function(NULL),
//          m_scc(),
//          m_phiVars(),
//          m_boundedIntegers(boundedIntegers),
//          m_unsignedEncoding(unsignedEncoding),
//          m_bitwidthMap(),
//          m_onlyLoopConditions(onlyLoopConditions),
//          m_loopConditionBlocks(),
//          m_divisionConstraintType(divisionConstraintType),
//          m_bitwiseConditions(bitwiseConditions),
//          m_complexityTuples(complexityTuples),
//          m_complexityLHSs(),
//          m_t2Output(t2Output)
//{
//}
Converter::Converter(const llvm::Type *boolType, bool assumeIsControl, bool selectIsControl, bool onlyMultiPredIsControl, bool boundedIntegers, bool unsignedEncoding, bool onlyLoopConditions, DivRemConstraintType divisionConstraintType, bool bitwiseConditions, bool complexityTuples, const bool t2Output, bool signednessInfo, bool nondetTypeInfo, bool unreachableExit)
    : m_entryBlock(NULL),
      m_boolType(boolType),
      m_blockRules(),
      m_rules(),
      m_vars(),
      m_lhs(),
      m_counter(0),
      m_phase1(true),
      m_globals(),
      m_mmMap(),
      m_funcMayZap(),
      m_tfMap(),
      m_elcMap(),
      m_returns(),
      m_idMap(),
      m_phiMap(),
      m_nondef(0),
      m_assumeIsControl(assumeIsControl),
      m_selectIsControl(selectIsControl),
      m_onlyMultiPredIsControl(onlyMultiPredIsControl),
      m_controlPoints(),
      m_trivial(false),
      m_function(NULL),
      m_scc(),
      m_phiVars(),
      m_boundedIntegers(boundedIntegers),
      m_unsignedEncoding(unsignedEncoding),
      m_bitwidthMap(),
      m_onlyLoopConditions(onlyLoopConditions),
      m_loopConditionBlocks(),
      m_divisionConstraintType(divisionConstraintType),
      m_bitwiseConditions(bitwiseConditions),
      m_complexityTuples(complexityTuples),
      m_complexityLHSs(),
      m_t2Output(t2Output),
      signednessInfo(signednessInfo),
      nondetTypeInfo(nondetTypeInfo),
      unreachableExit(unreachableExit)
{
}
//</Negar>

bool Converter::isTrivial(void)
{
    llvm::SmallVector<std::pair<const llvm::BasicBlock *, const llvm::BasicBlock *>, SMALL_VECTOR_SIZE> res;
    llvm::FindFunctionBackedges(*m_function, res);

    if (res.empty())
    {
        // no backedge
        for (llvm::Function::iterator bb = m_function->begin(), end = m_function->end(); bb != end; ++bb)
        {
            for (llvm::BasicBlock::iterator i = bb->begin(), e = bb->end(); i != e; ++i)
            {
                if (llvm::isa<llvm::CallInst>(i))
                {
                    llvm::CallInst *ci = llvm::cast<llvm::CallInst>(i);
                    llvm::Function *calledFunction = ci->getCalledFunction();
                    std::list<llvm::Function *> callees;
                    if (calledFunction != NULL)
                    {
                        callees.push_back(calledFunction);
                    }
                    else
                    {
                        callees = getMatchingFunctions(*ci);
                    }
                    for (std::list<llvm::Function *>::iterator cf = callees.begin(), cfe = callees.end(); cf != cfe; ++cf)
                    {
                        llvm::Function *callee = *cf;
                        if (m_scc.find(callee) != m_scc.end())
                        {
                            // call within SCC
                            return false;
                        }
                    }
                }
            }
        }
        return true;
    }
    else
    {
        // backedge
        return false;
    }
}

void Converter::phase1(llvm::Function *function, std::set<llvm::Function *> &scc, MayMustMap &mmMap, std::map<llvm::Function *, std::set<llvm::GlobalVariable *>> &funcMayZap, TrueFalseMap &tfMap, std::set<llvm::BasicBlock *> &lcbs, ConditionMap &elcMap)
{
    m_function = function;
    m_scc = scc;
    m_mmMap = mmMap;
    m_tfMap = tfMap;
    m_funcMayZap = funcMayZap;
    m_loopConditionBlocks = lcbs;
    m_elcMap = elcMap;
    m_globals.clear();
    m_blockRules.clear();
    m_rules.clear();
    m_vars.clear();
    m_lhs.clear();
    m_returns.clear();
    m_idMap.clear();
    m_phiMap.clear();
    m_phiVars.clear();
    m_controlPoints.clear();
    m_controlPoints.insert(getEval(m_function, "start"));
    m_controlPoints.insert(getEval(m_function, "stop"));
    m_counter = 0;
    m_nondef = 0;
    m_entryBlock = &function->getEntryBlock();
    m_trivial = isTrivial();

    for (llvm::Function::arg_iterator i = function->arg_begin(), e = function->arg_end(); i != e; ++i)
    {
        if (i->getType()->isIntegerTy() && i->getType() != m_boolType)
        {
            m_vars.push_back(getVar(i));
        }
    }
    llvm::Module *module = function->getParent();
    for (llvm::Module::global_iterator global = module->global_begin(), globale = module->global_end(); global != globale; ++global)
    {
        const llvm::Type *globalType = llvm::cast<llvm::PointerType>(global->getType())->getContainedType(0);
        if (globalType->isIntegerTy() && globalType != m_boolType)
        {
            std::string var = getVar(global);
            m_globals.push_back(global);
            m_vars.push_back(var);
            if (m_boundedIntegers)
            {
                m_bitwidthMap.insert(std::make_pair(var, llvm::cast<llvm::IntegerType>(globalType)->getBitWidth()));
            }
        }
    }

    //<Negar>
    for (llvm::Function &F : *module) {
        if (F.isDeclaration()) {
            continue;
        }
        for (llvm::BasicBlock &BB : F) {
            //if (llvm::isa<llvm::UnreachableInst>(BB.getTerminator())) {
            //    hasUnreachableBlock = true;
            //}
            lastBasicBlockName = BB.getName().str();
            for (llvm::Instruction &I : BB) {
                if (llvm::PHINode *phiNode = llvm::dyn_cast<llvm::PHINode>(&I)) {
                    if (phiNode->getType() == m_boolType || !phiNode->getType()->isIntegerTy()) {
                        std::string variable = phiNode->getName().str();
                        for (unsigned i = 0; i < phiNode->getNumIncomingValues(); ++i) {
                            PhiInst phiInst;
                            phiInst.variable = "v" + variable;
                            llvm::Value *value = phiNode->getIncomingValue(i);
                            std::string valueStr;
                            if (value->hasName()) {
                                valueStr = "v" + value->getName().str();
                            }
                            else {
                                llvm::raw_string_ostream rso(valueStr);
                                value->print(rso);
                                rso.flush();
                                size_t spacePos = valueStr.find(' ');
                                valueStr = (valueStr.find(' ') != std::string::npos) ? valueStr.substr(spacePos + 1) : valueStr;
                            }
                            phiInst.value = valueStr;
                            phiInst.basicBlock = phiNode->getIncomingBlock(i)->getName().str();
                            phiInsts.push_back(phiInst);
                        }
                    }
                }
            }
        }
    }

    for (const llvm::GlobalVariable& GV : module->globals()) {
        std::string varName = GV.getName().str();
        if (varName.find(".str") == std::string::npos && varName.find("__PRETTY_FUNCTION__.") == std::string::npos) {
            llvm::Type *varType = GV.getType()->getPointerElementType();
            if (varType->isArrayTy()) {
                if (GV.isConstant()) {
                    // Define an array -> Globally -> One-dimensional -> 2
                    std::string arrayName = "v" + varName;
                    globalInsts.push_back(arrayName + " := nondet();");
                    if (auto *dataArray = llvm::dyn_cast<llvm::ConstantDataArray>(const_cast<llvm::Constant *>(GV.getInitializer()))) {
                        if (dataArray->isString()) {
                            std::string dataArrayStr = dataArray->getAsString();
                            for (unsigned i = 0; i < dataArrayStr.size(); ++i) {
                                std::string value;
                                switch (dataArrayStr[i]) {
                                    case '\n':
                                        value = "\'\\n\'";
                                        break;
                                    case '\0':
                                        value = "\'\\0\'";
                                        break;
                                    default:
                                        break;
                                }
                                globalInsts.push_back(arrayName + " := store_array(" + arrayName + ", " + std::to_string(i) + ", " + value + ");");
                            }
                        }
                    }
                    if (std::find(oneDimArrs.begin(), oneDimArrs.end(), arrayName) == oneDimArrs.end()) {
                        oneDimArrs.push_back(arrayName);
                    }
                }
                else {
                    // Define an array -> Globally -> One-dimensional -> 1
                    std::string arrayName = "v" + varName;
                    //if (globalVar.hasInitializer() && llvm::isa<llvm::ConstantAggregateZero>(const_cast<llvm::Constant *>(globalVar.getInitializer()))) {
                    //    globalInsts.push_back(arrayName + " := const_array(0);");
                    //}
                    //else {
                    globalInsts.push_back("v" + varName + " := nondet();");
                    //}
                    if (std::find(oneDimArrs.begin(), oneDimArrs.end(), arrayName) == oneDimArrs.end()) {
                        oneDimArrs.push_back(arrayName);
                    }
                }
            }
            else {
                // Define global variable
                if (GV.hasInitializer()) {
                    varName.erase(std::remove(varName.begin(), varName.end(), '\''), varName.end());
                    llvm::ConstantInt* initOperand = llvm::dyn_cast<llvm::ConstantInt>(const_cast<llvm::Constant *>(GV.getInitializer()));
                    globalInsts.push_back(varName + " := " + std::to_string(initOperand->getZExtValue()) + ";");
                }
            }
        }
    }
    //</Negar>

    if (!m_trivial)
    {
        m_phase1 = true;
        visit(function);
    }

    for (std::list<std::string>::iterator i = m_vars.begin(), e = m_vars.end(); i != e; ++i)
    {
        m_lhs.push_back(Polynomial::create(*i));
    }
}

void Converter::phase2(llvm::Function *function, std::set<llvm::Function *> &scc, MayMustMap &mmMap, std::map<llvm::Function *, std::set<llvm::GlobalVariable *>> &funcMayZap, TrueFalseMap &tfMap, std::set<llvm::BasicBlock *> &lcbs, ConditionMap &elcMap)
{
    if (m_trivial)
    {
        m_rules.push_back(Rule::create(Term::create(getEval(m_function, "start"), m_lhs), Term::create(getEval(m_function, "stop"), m_lhs), Constraint::_true));
        return;
    }
    m_function = function;
    m_scc = scc;
    m_mmMap = mmMap;
    m_tfMap = tfMap;
    m_funcMayZap = funcMayZap;
    m_loopConditionBlocks = lcbs;
    m_elcMap = elcMap;
    m_phase1 = false;

    for (llvm::Function::iterator bb = m_function->begin(), end = m_function->end(); bb != end; ++bb)
    {
        visitBB(bb);
    }

    // add rules from returns to stop
    for (std::list<llvm::BasicBlock *>::iterator i = m_returns.begin(), e = m_returns.end(); i != e; ++i)
    {
        ref<Term> lhs = Term::create(getEval(*i, "out"), m_lhs);
        ref<Term> rhs = Term::create(getEval(m_function, "stop"), m_lhs);
        ref<Rule> rule = Rule::create(lhs, rhs, Constraint::_true);
        m_rules.push_back(rule);
    }
}

std::list<ref<Rule>> Converter::getRules()
{
    return m_rules;
}

std::list<ref<Rule>> Converter::getCondensedRules()
{
    std::list<ref<Rule>> good;
    std::list<ref<Rule>> junk;
    std::list<ref<Rule>> res;
    for (std::list<ref<Rule>>::iterator i = m_rules.begin(), e = m_rules.end(); i != e; ++i)
    {
        ref<Rule> rule = *i;
        std::string f = rule->getLeft()->getFunctionSymbol();
        if (m_controlPoints.find(f) != m_controlPoints.end())
        {
            good.push_back(rule);
        }
        else
        {
            junk.push_back(rule);
        }
    }
    for (std::list<ref<Rule>>::iterator i = good.begin(), e = good.end(); i != e; ++i)
    {
        ref<Rule> rule = *i;
        std::vector<ref<Rule>> todo;
        todo.push_back(rule);
        while (!todo.empty())
        {
            ref<Rule> r = *todo.begin();
            todo.erase(todo.begin());
            ref<Term> rhs = r->getRight();
            std::string f = rhs->getFunctionSymbol();
            if (m_controlPoints.find(f) != m_controlPoints.end())
            {
                res.push_back(r);
            }
            else
            {
                std::list<ref<Rule>> newtodo;
                for (std::list<ref<Rule>>::iterator ii = junk.begin(), ee = junk.end(); ii != ee; ++ii)
                {
                    ref<Rule> junkrule = *ii;
                    if (junkrule->getLeft()->getFunctionSymbol() == f)
                    {
                        std::map<std::string, ref<Polynomial>> subby;
                        std::list<ref<Polynomial>> rhsargs = rhs->getArgs();
                        std::list<ref<Polynomial>>::iterator ai = rhsargs.begin();
                        for (std::list<std::string>::iterator vi = m_vars.begin(), ve = m_vars.end(); vi != ve; ++vi, ++ai)
                        {
                            subby.insert(std::make_pair(*vi, *ai));
                        }
                        ref<Rule> newRule = Rule::create(r->getLeft(), junkrule->getRight()->instantiate(&subby), Operator::create(r->getConstraint(), junkrule->getConstraint()->instantiate(&subby), Operator::And));
                        newtodo.push_back(newRule);
                    }
                }
                todo.insert(todo.begin(), newtodo.begin(), newtodo.end());
            }
        }
    }
    return res;
}

std::string Converter::getVar(llvm::Value *V)
{
    std::string name = V->getName();
    if (!name.empty() && name[0] == '\'')
    {
        name = name.substr(1);
    }
    else
    {
        name = "v" + name;
    }
    std::ostringstream tmp;
    tmp << name;
    std::string res = tmp.str();
    if (m_boundedIntegers && V->getType()->isIntegerTy())
    {
        m_bitwidthMap.insert(std::make_pair(res, llvm::cast<llvm::IntegerType>(V->getType())->getBitWidth()));
    }
    return res;
}

std::string Converter::getEval(unsigned int i)
{
    std::ostringstream tmp;
    tmp << "eval_" << m_function->getName().str() << "_" << i;
    return tmp.str();
}

std::string Converter::getEval(llvm::BasicBlock *bb, std::string inout)
{
    std::ostringstream tmp;
    tmp << "eval_" << bb->getName().str() << '_' << inout;
    std::string res = tmp.str();
    if (inout == "in" && (!m_onlyMultiPredIsControl || bb->getUniquePredecessor() == NULL))
    {
        m_controlPoints.insert(res);
    }
    return res;
}

std::string Converter::getEval(llvm::Function *func, std::string startstop)
{
    std::ostringstream tmp;
    tmp << "eval_" << func->getName().str() << "_" << startstop;
    return tmp.str();
}

ref<Polynomial> Converter::getPolynomial(llvm::Value *V)
{
    if (llvm::isa<llvm::ConstantInt>(V))
    {
        mpz_t value;
        mpz_init(value);
        if (m_boundedIntegers && m_unsignedEncoding)
        {
            uint64_t cv = static_cast<llvm::ConstantInt *>(V)->getZExtValue();
            std::ostringstream tmp;
            tmp << cv;
            gmp_sscanf(tmp.str().data(), "%Zu", value);
        }
        else
        {
            int64_t cv = static_cast<llvm::ConstantInt *>(V)->getSExtValue();
            std::ostringstream tmp;
            tmp << cv;
            gmp_sscanf(tmp.str().data(), "%Zd", value);
        }
        ref<Polynomial> res = Polynomial::create(value);
        mpz_clear(value);
        return res;
    }
    else if (llvm::isa<llvm::Instruction>(V) || llvm::isa<llvm::Argument>(V) || llvm::isa<llvm::GlobalVariable>(V))
    {
        std::string res = getVar(V);
        return Polynomial::create(getVar(V));
    }
    else
    {
        return Polynomial::create(getNondef(V));
    }
}

std::list<ref<Polynomial>> Converter::getNewArgs(llvm::Value &V, ref<Polynomial> p)
{
    std::list<ref<Polynomial>> res;
    std::string Vname = getVar(&V);
    std::list<ref<Polynomial>>::iterator pp = m_lhs.begin();
    for (std::list<std::string>::iterator i = m_vars.begin(), e = m_vars.end(); i != e; ++i, ++pp)
    {
        if (Vname == *i)
        {
            res.push_back(p);
        }
        else
        {
            res.push_back(*pp);
        }
    }
    return res;
}

std::list<ref<Polynomial>> Converter::getZappedArgs(std::set<llvm::GlobalVariable *> toZap)
{
    std::list<ref<Polynomial>> res;
    std::list<ref<Polynomial>>::iterator pp = m_lhs.begin();
    for (std::list<std::string>::iterator i = m_vars.begin(), e = m_vars.end(); i != e; ++i, ++pp)
    {
        bool doZap = false;
        const llvm::Type *zapType = NULL;
        for (std::set<llvm::GlobalVariable *>::iterator zap = toZap.begin(), zape = toZap.end(); zap != zape; ++zap)
        {
            if (getVar(*zap) == *i)
            {
                doZap = true;
                zapType = llvm::cast<llvm::PointerType>((*zap)->getType())->getContainedType(0);
                break;
            }
        }
        if (doZap)
        {
            std::string nondef = getNondef(NULL);
            if (m_boundedIntegers)
            {
                m_bitwidthMap.insert(std::make_pair(nondef, llvm::cast<llvm::IntegerType>(zapType)->getBitWidth()));
            }
            res.push_back(Polynomial::create(nondef));
        }
        else
        {
            res.push_back(*pp);
        }
    }
    return res;
}

std::list<ref<Polynomial>> Converter::getZappedArgs(std::set<llvm::GlobalVariable *> toZap, llvm::Value &V, ref<Polynomial> p)
{
    std::list<ref<Polynomial>> res;
    std::string Vname = getVar(&V);
    std::list<ref<Polynomial>>::iterator pp = m_lhs.begin();
    for (std::list<std::string>::iterator i = m_vars.begin(), e = m_vars.end(); i != e; ++i, ++pp)
    {
        bool doZap = false;
        const llvm::Type *zapType = NULL;
        for (std::set<llvm::GlobalVariable *>::iterator zap = toZap.begin(), zape = toZap.end(); zap != zape; ++zap)
        {
            if (getVar(*zap) == *i)
            {
                doZap = true;
                zapType = llvm::cast<llvm::PointerType>((*zap)->getType())->getContainedType(0);
                break;
            }
        }
        if (doZap)
        {
            std::string nondef = getNondef(NULL);
            if (m_boundedIntegers)
            {
                m_bitwidthMap.insert(std::make_pair(nondef, llvm::cast<llvm::IntegerType>(zapType)->getBitWidth()));
            }
            res.push_back(Polynomial::create(nondef));
        }
        else if (Vname == *i)
        {
            res.push_back(p);
        }
        else
        {
            res.push_back(*pp);
        }
    }
    return res;
}

ref<Constraint> Converter::getConditionFromValue(llvm::Value *cond)
{
    if (llvm::isa<llvm::ConstantInt>(cond))
    {
        return Atom::create(getPolynomial(cond), Polynomial::null, Atom::Neq);
    }
    if (llvm::isa<llvm::Argument>(cond) && cond->getType() == m_boolType)
    {
        return Nondef::create();
    }
    if (!llvm::isa<llvm::Instruction>(cond))
    {
        cond->dump();
        std::cerr << "Cannot handle non-instructions!" << std::endl;
        exit(5);
    }
    llvm::Instruction *I = llvm::cast<llvm::Instruction>(cond);
    return getConditionFromInstruction(I);
}

ref<Constraint> Converter::getConditionFromInstruction(llvm::Instruction *I)
{
    if (llvm::isa<llvm::ZExtInst>(I))
    {
        return getConditionFromValue(I->getOperand(0));
    }
    if (I->getType() != m_boolType)
    {
        return Atom::create(getPolynomial(I), Polynomial::null, Atom::Neq);
    }
    if (llvm::isa<llvm::CmpInst>(I))
    {
        llvm::CmpInst *cmp = llvm::cast<llvm::CmpInst>(I);
        if (cmp->getOperand(0)->getType()->isPointerTy())
        {
            return Nondef::create();
        }
        else if (cmp->getOperand(0)->getType()->isFloatingPointTy())
        {
            return Nondef::create();
        }
        else
        {
            llvm::CmpInst::Predicate pred = cmp->getPredicate();
            if (m_boundedIntegers && !m_unsignedEncoding && (pred == llvm::CmpInst::ICMP_UGT || pred == llvm::CmpInst::ICMP_UGE || pred == llvm::CmpInst::ICMP_ULT || pred == llvm::CmpInst::ICMP_ULE))
            {
                return getUnsignedComparisonForSignedBounded(pred, getPolynomial(cmp->getOperand(0)), getPolynomial(cmp->getOperand(1)));
            }
            else if (m_boundedIntegers && m_unsignedEncoding && (pred == llvm::CmpInst::ICMP_SGT || pred == llvm::CmpInst::ICMP_SGE || pred == llvm::CmpInst::ICMP_SLT || pred == llvm::CmpInst::ICMP_SLE))
            {
                unsigned int bitwidth = llvm::cast<llvm::IntegerType>(cmp->getOperand(0)->getType())->getBitWidth();
                return getSignedComparisonForUnsignedBounded(pred, getPolynomial(cmp->getOperand(0)), getPolynomial(cmp->getOperand(1)), bitwidth);
            }
            else
            {
                return Atom::create(getPolynomial(cmp->getOperand(0)), getPolynomial(cmp->getOperand(1)), getAtomType(pred));
            }
        }
    }
    std::string opcodeName = I->getOpcodeName();
    if (opcodeName == "and")
    {
        return Operator::create(getConditionFromValue(I->getOperand(0)), getConditionFromValue(I->getOperand(1)), Operator::And);
    }
    else if (opcodeName == "or")
    {
        return Operator::create(getConditionFromValue(I->getOperand(0)), getConditionFromValue(I->getOperand(1)), Operator::Or);
    }
    else if (opcodeName == "xor")
    {
        llvm::ConstantInt *ci;
        unsigned int realIdx;
        if (llvm::isa<llvm::ConstantInt>(I->getOperand(0)))
        {
            ci = llvm::cast<llvm::ConstantInt>(I->getOperand(0));
            realIdx = 1;
        }
        else
        {
            ci = llvm::cast<llvm::ConstantInt>(I->getOperand(1));
            realIdx = 0;
        }
        if (ci->isOne())
        {
            return Negation::create(getConditionFromValue(I->getOperand(realIdx)));
        }
        else
        {
            return getConditionFromValue(I->getOperand(realIdx));
        }
    }
    else if (opcodeName == "select")
    {
        llvm::ConstantInt *opOne = llvm::dyn_cast<llvm::ConstantInt>(I->getOperand(1));
        llvm::ConstantInt *opTwo = llvm::dyn_cast<llvm::ConstantInt>(I->getOperand(2));
        if (opOne != NULL && opOne->isOne() && opTwo != NULL && !opTwo->isOne())
        {
            // select ... true false (this actually occurs in some bitcode)
            return getConditionFromValue(I->getOperand(0));
        }
        else if (opOne != NULL && opOne->isOne())
        {
            // select ... true ...
            // true --> or
            return Operator::create(getConditionFromValue(I->getOperand(0)), getConditionFromValue(I->getOperand(2)), Operator::Or);
        }
        else if (opTwo != NULL && !opTwo->isOne())
        {
            // select ... ... false
            return Operator::create(getConditionFromValue(I->getOperand(0)), getConditionFromValue(I->getOperand(1)), Operator::And);
        }
        else
        {
            // select ... ... ...
            ref<Constraint> test = getConditionFromValue(I->getOperand(0));
            ref<Constraint> negTest = Negation::create(test);
            ref<Constraint> truePart = Operator::create(test, getConditionFromValue(I->getOperand(1)), Operator::And);
            ref<Constraint> falsePart = Operator::create(negTest, getConditionFromValue(I->getOperand(2)), Operator::And);
            return Operator::create(truePart, falsePart, Operator::Or);
        }
    }
    else
    {
        return Nondef::create();
    }
}

ref<Constraint> Converter::getUnsignedComparisonForSignedBounded(llvm::CmpInst::Predicate pred, ref<Polynomial> x, ref<Polynomial> y)
{
    switch (pred)
    {
    case llvm::CmpInst::ICMP_UGT:
    case llvm::CmpInst::ICMP_UGE:
    {
        //<Negar>
        ref<Constraint> xge;
        ref<Constraint> yge;
        ref<Constraint> xlt;
        ref<Constraint> ylt;
        if (signednessInfo) {
            xge = Atom::create(x, Polynomial::null, Atom::Uge);
            yge = Atom::create(y, Polynomial::null, Atom::Uge);
            xlt = Atom::create(x, Polynomial::null, Atom::Ult);
            ylt = Atom::create(y, Polynomial::null, Atom::Ult);
        }
        else {
            xge = Atom::create(x, Polynomial::null, Atom::Geq);
            yge = Atom::create(y, Polynomial::null, Atom::Geq);
            xlt = Atom::create(x, Polynomial::null, Atom::Lss);
            ylt = Atom::create(y, Polynomial::null, Atom::Lss);
        }
        //</Negar>
        ref<Constraint> gege = Operator::create(xge, yge, Operator::And);
        ref<Constraint> ltlt = Operator::create(xlt, ylt, Operator::And);
        ref<Constraint> ltge = Operator::create(xlt, yge, Operator::And);
        ref<Constraint> disj1 = Operator::create(gege, Atom::create(x, y, getAtomType(pred)), Operator::And);
        ref<Constraint> disj2 = Operator::create(ltlt, Atom::create(x, y, getAtomType(pred)), Operator::And);
        ref<Constraint> disj3 = ltge;
        ref<Constraint> tmp = Operator::create(disj1, disj2, Operator::Or);
        return Operator::create(tmp, disj3, Operator::Or);
    }
    case llvm::CmpInst::ICMP_ULT:
        return getUnsignedComparisonForSignedBounded(llvm::CmpInst::ICMP_UGT, y, x);
    case llvm::CmpInst::ICMP_ULE:
        return getUnsignedComparisonForSignedBounded(llvm::CmpInst::ICMP_UGE, y, x);
    case llvm::CmpInst::ICMP_EQ:
    case llvm::CmpInst::ICMP_NE:
    case llvm::CmpInst::ICMP_SGT:
    case llvm::CmpInst::ICMP_SGE:
    case llvm::CmpInst::ICMP_SLT:
    case llvm::CmpInst::ICMP_SLE:
    case llvm::CmpInst::BAD_ICMP_PREDICATE:
    case llvm::CmpInst::FCMP_FALSE:
    case llvm::CmpInst::FCMP_OEQ:
    case llvm::CmpInst::FCMP_OGT:
    case llvm::CmpInst::FCMP_OGE:
    case llvm::CmpInst::FCMP_OLT:
    case llvm::CmpInst::FCMP_OLE:
    case llvm::CmpInst::FCMP_ONE:
    case llvm::CmpInst::FCMP_ORD:
    case llvm::CmpInst::FCMP_UNO:
    case llvm::CmpInst::FCMP_UEQ:
    case llvm::CmpInst::FCMP_UGT:
    case llvm::CmpInst::FCMP_UGE:
    case llvm::CmpInst::FCMP_ULT:
    case llvm::CmpInst::FCMP_ULE:
    case llvm::CmpInst::FCMP_UNE:
    case llvm::CmpInst::FCMP_TRUE:
    case llvm::CmpInst::BAD_FCMP_PREDICATE:
    default:
        std::cerr << "Unexpected unsigned comparison predicate" << std::endl;
        exit(7);
    }
}

ref<Constraint> Converter::getSignedComparisonForUnsignedBounded(llvm::CmpInst::Predicate pred, ref<Polynomial> x, ref<Polynomial> y, unsigned int bitwidth)
{
    ref<Polynomial> maxpos = Polynomial::simax(bitwidth);
    switch (pred)
    {
    case llvm::CmpInst::ICMP_SGT:
    case llvm::CmpInst::ICMP_SGE:
    {
        //<Negar>
        ref<Constraint> xle;
        ref<Constraint> yle;
        ref<Constraint> xgt;
        ref<Constraint> ygt;
        if (signednessInfo) {
            xle = Atom::create(x, maxpos, Atom::Sle);
            yle = Atom::create(y, maxpos, Atom::Sle);
            xgt = Atom::create(x, maxpos, Atom::Sgt);
            ygt = Atom::create(y, maxpos, Atom::Sgt);
        }
        else {
            xle = Atom::create(x, maxpos, Atom::Leq);
            yle = Atom::create(y, maxpos, Atom::Leq);
            xgt = Atom::create(x, maxpos, Atom::Gtr);
            ygt = Atom::create(y, maxpos, Atom::Gtr);
        }
        //</Negar>
        ref<Constraint> lele = Operator::create(xle, yle, Operator::And);
        ref<Constraint> gtgt = Operator::create(xgt, ygt, Operator::And);
        ref<Constraint> legt = Operator::create(xle, ygt, Operator::And);
        ref<Constraint> disj1 = Operator::create(lele, Atom::create(x, y, getAtomType(pred)), Operator::And);
        ref<Constraint> disj2 = Operator::create(gtgt, Atom::create(x, y, getAtomType(pred)), Operator::And);
        ref<Constraint> disj3 = legt;
        ref<Constraint> tmp = Operator::create(disj1, disj2, Operator::Or);
        return Operator::create(tmp, disj3, Operator::Or);
    }
    case llvm::CmpInst::ICMP_SLT:
        return getSignedComparisonForUnsignedBounded(llvm::CmpInst::ICMP_SGT, y, x, bitwidth);
    case llvm::CmpInst::ICMP_SLE:
        return getSignedComparisonForUnsignedBounded(llvm::CmpInst::ICMP_SGE, y, x, bitwidth);
    case llvm::CmpInst::ICMP_EQ:
    case llvm::CmpInst::ICMP_NE:
    case llvm::CmpInst::ICMP_UGT:
    case llvm::CmpInst::ICMP_UGE:
    case llvm::CmpInst::ICMP_ULT:
    case llvm::CmpInst::ICMP_ULE:
    case llvm::CmpInst::BAD_ICMP_PREDICATE:
    case llvm::CmpInst::FCMP_FALSE:
    case llvm::CmpInst::FCMP_OEQ:
    case llvm::CmpInst::FCMP_OGT:
    case llvm::CmpInst::FCMP_OGE:
    case llvm::CmpInst::FCMP_OLT:
    case llvm::CmpInst::FCMP_OLE:
    case llvm::CmpInst::FCMP_ONE:
    case llvm::CmpInst::FCMP_ORD:
    case llvm::CmpInst::FCMP_UNO:
    case llvm::CmpInst::FCMP_UEQ:
    case llvm::CmpInst::FCMP_UGT:
    case llvm::CmpInst::FCMP_UGE:
    case llvm::CmpInst::FCMP_ULT:
    case llvm::CmpInst::FCMP_ULE:
    case llvm::CmpInst::FCMP_UNE:
    case llvm::CmpInst::FCMP_TRUE:
    case llvm::CmpInst::BAD_FCMP_PREDICATE:
    default:
        std::cerr << "Unexpected signed comparison predicate" << std::endl;
        exit(7);
    }
}

Atom::AType Converter::getAtomType(llvm::CmpInst::Predicate pred)
{
    switch (pred)
    {
    case llvm::CmpInst::ICMP_EQ:
        return Atom::Equ;
    case llvm::CmpInst::ICMP_NE:
        return Atom::Neq;
    //<Negar>
    case llvm::CmpInst::ICMP_SLT:
        if (signednessInfo) {
            return Atom::Slt;
        }
        else {
            return Atom::Lss;
        }
    case llvm::CmpInst::ICMP_ULT:
        if (signednessInfo) {
            return Atom::Ult;
        }
        else {
            return Atom::Lss;
        }
    case llvm::CmpInst::ICMP_SLE:
        if (signednessInfo) {
            return Atom::Sle;
        }
        else {
            return Atom::Leq;
        }
    case llvm::CmpInst::ICMP_ULE:
        if (signednessInfo) {
            return Atom::Ule;
        }
        else {
            return Atom::Leq;
        }
    case llvm::CmpInst::ICMP_SGT:
        if (signednessInfo) {
            return Atom::Sgt;
        }
        else {
            return Atom::Gtr;
        }
    case llvm::CmpInst::ICMP_UGT:
        if (signednessInfo) {
            return Atom::Ugt;
        }
        else {
            return Atom::Gtr;
        }
    case llvm::CmpInst::ICMP_SGE:
        if (signednessInfo) {
            return Atom::Sge;
        }
        else {
            return Atom::Geq;
        }
    case llvm::CmpInst::ICMP_UGE:
        if (signednessInfo) {
            return Atom::Uge;
        }
        else {
            return Atom::Geq;
        }
    //</Negar>
    case llvm::CmpInst::BAD_ICMP_PREDICATE:
    case llvm::CmpInst::FCMP_FALSE:
    case llvm::CmpInst::FCMP_OEQ:
    case llvm::CmpInst::FCMP_OGT:
    case llvm::CmpInst::FCMP_OGE:
    case llvm::CmpInst::FCMP_OLT:
    case llvm::CmpInst::FCMP_OLE:
    case llvm::CmpInst::FCMP_ONE:
    case llvm::CmpInst::FCMP_ORD:
    case llvm::CmpInst::FCMP_UNO:
    case llvm::CmpInst::FCMP_UEQ:
    case llvm::CmpInst::FCMP_UGT:
    case llvm::CmpInst::FCMP_UGE:
    case llvm::CmpInst::FCMP_ULT:
    case llvm::CmpInst::FCMP_ULE:
    case llvm::CmpInst::FCMP_UNE:
    case llvm::CmpInst::FCMP_TRUE:
    case llvm::CmpInst::BAD_FCMP_PREDICATE:
    default:
        std::cerr << "Unknown comparison predicate" << std::endl;
        exit(7);
    }
}

ref<Constraint> Converter::buildConjunction(std::set<llvm::Value *> &trues, std::set<llvm::Value *> &falses)
{
    ref<Constraint> res = Constraint::_true;
    for (std::set<llvm::Value *>::iterator i = trues.begin(), e = trues.end(); i != e; ++i)
    {
        ref<Constraint> c = getConditionFromValue(*i)->toNNF(false);
        res = Operator::create(res, c, Operator::And);
    }
    for (std::set<llvm::Value *>::iterator i = falses.begin(), e = falses.end(); i != e; ++i)
    {
        ref<Constraint> c = getConditionFromValue(*i)->toNNF(true);
        res = Operator::create(res, c, Operator::And);
    }
    return res;
}

ref<Constraint> Converter::buildBoundConjunction(std::set<quadruple<llvm::Value *, llvm::CmpInst::Predicate, llvm::Value *, llvm::Value *>> &bounds)
{
    ref<Constraint> res = Constraint::_true;
    for (std::set<quadruple<llvm::Value *, llvm::CmpInst::Predicate, llvm::Value *, llvm::Value *>>::iterator i = bounds.begin(), e = bounds.end(); i != e; ++i)
    {
        ref<Polynomial> p = getPolynomial(i->first);
        ref<Polynomial> q1 = getPolynomial(i->third);
        ref<Polynomial> q2 = getPolynomial(i->fourth);
        ref<Constraint> c = Atom::create(p, q1->add(q2), getAtomType(i->second));
        res = Operator::create(res, c, Operator::And);
    }
    return res;
}

void Converter::visitBB(llvm::BasicBlock *bb)
{
    // start
    if (bb == m_entryBlock)
    {
        ref<Term> lhs = Term::create(getEval(m_function, "start"), m_lhs);
        ref<Term> rhs = Term::create(getEval(bb, "in"), m_lhs);
        ref<Rule> rule = Rule::create(lhs, rhs, Constraint::_true);
        m_rules.push_back(rule);

        if (!m_phase1 && m_t2Output)
        {
            std::cout << "START: " << (bb->getName().str()) << ";" << std::endl
                      << std::endl;

            //<Negar>
            //if (hasUnreachableBlock) {
            //    std::cout << "ERROR: 1;" << std::endl << std::endl;
            //}
            //</Negar>
        }
    }

    if (!m_phase1 && m_t2Output)
    {
        std::cout << "FROM: " << (bb->getName().str()) << ";" << std::endl;

        //<Negar>
        if (isEntryBlock == true) {
            for (const std::string& globalInst : globalInsts) {
                std::cout << globalInst << std::endl;
            }
            isEntryBlock = false;
        }
        //</Negar>
    }

    // return
    if (llvm::isa<llvm::ReturnInst>(bb->getTerminator()))
    {
        m_returns.push_back(bb);
    }

    // visit instructions
    m_blockRules.clear();
    visit(*bb);

    // jump from bb_in to first instruction or bb_out
    // get condition
    ref<Constraint> cond;
    TrueFalseMap::iterator it = m_tfMap.find(bb);
    if (it != m_tfMap.end())
    {
        TrueFalsePair tfp = it->second;
        std::set<llvm::Value *> trues = tfp.first;
        std::set<llvm::Value *> falses = tfp.second;
        cond = buildConjunction(trues, falses);
    }
    else
    {
        cond = Constraint::_true;
    }
    ConditionMap::iterator it2 = m_elcMap.find(bb);
    if (it2 != m_elcMap.end())
    {
        std::set<quadruple<llvm::Value *, llvm::CmpInst::Predicate, llvm::Value *, llvm::Value *>> bounds = it2->second;
        ref<Constraint> c_new = buildBoundConjunction(bounds);
        cond = Operator::create(cond, c_new, Operator::And);
    }
    // find first instruction
    llvm::Instruction *first = NULL;
    unsigned int firstID = 0;
    for (llvm::BasicBlock::iterator i = bb->begin(), e = bb->end(); i != e; ++i)
    {
        std::map<llvm::Instruction *, unsigned int>::iterator found = m_idMap.find(i);
        if (found != m_idMap.end())
        {
            first = i;
            firstID = found->second;
            break;
        }
    }
    if (first != NULL)
    {
        ref<Term> lhs = Term::create(getEval(bb, "in"), m_lhs);
        ref<Term> rhs = Term::create(getEval(firstID), m_lhs);
        ref<Rule> rule = Rule::create(lhs, rhs, cond);
        m_rules.push_back(rule);
    }
    else
    {
        ref<Term> lhs = Term::create(getEval(bb, "in"), m_lhs);
        ref<Term> rhs = Term::create(getEval(bb, "out"), m_lhs);
        ref<Rule> rule = Rule::create(lhs, rhs, cond);
        m_rules.push_back(rule);
    }

    // insert rules for instructions
    m_rules.insert(m_rules.end(), m_blockRules.begin(), m_blockRules.end());

    // jump from last instruction in bb to bb_out
    llvm::Instruction *last = NULL;
    unsigned int lastID = 0;
    for (llvm::BasicBlock::iterator i = bb->begin(), e = bb->end(); i != e; ++i)
    {
        // terminators are not in the map
        std::map<llvm::Instruction *, unsigned int>::iterator found = m_idMap.find(i);
        if (found != m_idMap.end())
        {
            last = i;
            lastID = found->second;
        }
    }
    if (last != NULL)
    {
        ref<Term> lhs = Term::create(getEval(lastID + 1), m_lhs);
        m_counter++;
        ref<Term> rhs = Term::create(getEval(bb, "out"), m_lhs);
        ref<Rule> rule = Rule::create(lhs, rhs, Constraint::_true);
        m_rules.push_back(rule);
    }

    // jump from bb_out to succs
    llvm::TerminatorInst *terminator = bb->getTerminator();
    if (llvm::isa<llvm::ReturnInst>(terminator))
    {
    }
    else if (llvm::isa<llvm::UnreachableInst>(terminator))
    {
        ref<Term> lhs = Term::create(getEval(bb, "out"), m_lhs);
        ref<Term> rhs = Term::create(getEval(m_function, "stop"), m_lhs);
        ref<Rule> rule = Rule::create(lhs, rhs, Constraint::_true);
        m_rules.push_back(rule);
    }
    else
    {
        llvm::BranchInst *branch = llvm::cast<llvm::BranchInst>(terminator);
        bool useCondition = (!m_onlyLoopConditions || m_loopConditionBlocks.find(bb) != m_loopConditionBlocks.end());
        if (branch->isUnconditional())
        {
            ref<Term> lhs = Term::create(getEval(bb, "out"), m_lhs);
            ref<Term> rhs = Term::create(getEval(branch->getSuccessor(0), "in"), getArgsWithPhis(bb, branch->getSuccessor(0)));
            ref<Rule> rule = Rule::create(lhs, rhs, Constraint::_true);
            m_rules.push_back(rule);
        }
        else
        {
            ref<Term> lhs = Term::create(getEval(bb, "out"), m_lhs);
            ref<Term> rhs1 = Term::create(getEval(branch->getSuccessor(0), "in"), getArgsWithPhis(bb, branch->getSuccessor(0)));
            ref<Term> rhs2 = Term::create(getEval(branch->getSuccessor(1), "in"), getArgsWithPhis(bb, branch->getSuccessor(1)));
            ref<Constraint> c = getConditionFromValue(branch->getCondition());
            ref<Rule> rule1 = Rule::create(lhs, rhs1, useCondition ? c->toNNF(false) : Constraint::_true);
            m_rules.push_back(rule1);
            ref<Rule> rule2 = Rule::create(lhs, rhs2, useCondition ? c->toNNF(true) : Constraint::_true);
            m_rules.push_back(rule2);
        }
    }
    if (m_t2Output)
    {
        std::cout << std::endl;
    }
}

std::list<ref<Polynomial>> Converter::getArgsWithPhis(llvm::BasicBlock *from, llvm::BasicBlock *to)
{
    std::list<ref<Polynomial>> res;
    std::map<std::string, ref<Polynomial>> phiValues;
    for (llvm::BasicBlock::iterator i = to->begin(), e = to->end(); i != e; ++i)
    {
        if (!llvm::isa<llvm::PHINode>(*i))
        {
            break;
        }
        llvm::PHINode *phi = llvm::cast<llvm::PHINode>(i);
        if (phi->getType() == m_boolType || !phi->getType()->isIntegerTy())
        {
            continue;
        }
        std::string PHIName = getVar(phi);
        phiValues.insert(std::make_pair(PHIName, getPolynomial(phi->getIncomingValueForBlock(from))));
    }
    std::list<ref<Polynomial>>::iterator pp = m_lhs.begin();
    for (std::list<std::string>::iterator i = m_vars.begin(), e = m_vars.end(); i != e; ++i, ++pp)
    {
        std::map<std::string, ref<Polynomial>>::iterator found = phiValues.find(*i);
        if (found == phiValues.end())
        {
            res.push_back(*pp);
        }
        else
        {
            res.push_back(found->second);
        }
    }
    return res;
}

void Converter::visitTerminatorInst(llvm::TerminatorInst &I)
{
    if (!m_phase1)
    {
        //This is a self loop to the last instruction.
        //ToDO: Remove the self-loop addition in T2 in these cases.
        if (llvm::isa<llvm::ReturnInst>(I))
        {
            llvm::BasicBlock *pBlock = I.getParent();
            if (m_t2Output)
            {
                std::string retNode = (pBlock->getName().str()) + "_ret";
                std::cout << "TO: " << retNode << ";" << std::endl;
            }
        }
        else if (llvm::isa<llvm::UnreachableInst>(I))
        {
            //<Negar>
            //std::cout << "TO: 1;" << std::endl;
            if (unreachableExit) {
                std::cout << "TO: " + lastBasicBlockName + "_ret;" << std::endl;
            }
            else {
                std::cout << "TO: " + I.getParent()->getName().str() + ";" << std::endl;
            }
            //</Negar>
        }
        else
        {
            //<Negar>
            const std::string &basicBlock = I.getParent()->getName().str();
            auto myIt = std::find_if(phiInsts.begin(), phiInsts.end(), [&basicBlock](const PhiInst& phiInst) { return phiInst.basicBlock == basicBlock; });
            if (myIt != phiInsts.end()) {
                std::cout << "var__temp_" << myIt->variable << " := " << myIt->value << ";" << std::endl;
            }
            //</Negar>

            int64_t cv;
            std::string valName;
            llvm::BranchInst *branch = llvm::cast<llvm::BranchInst>(&I);
            llvm::BasicBlock *pBlock = branch->getParent();

            //Indicates we've already passed Phase1, meaning before
            //transitioning to next block we must update the correct
            //phi variables which were collected in Phase1.
            std::map<llvm::BasicBlock *, std::list<std::pair<std::string, llvm::Value *>>>::iterator it = m_phiMap.find(pBlock);
            if (it != m_phiMap.end())
            {
                std::list<std::pair<std::string, llvm::Value *>>::iterator it2;

                //All phi-instructions at the beginning of a block are meant to be executed simultaneously.
                //To achieve this parallel assignment, we thus assign the fresh values to %var__temp
                //or all phi instructions, and then add a set of %var :=var__temp instructions.
                for (it2 = (m_phiMap[pBlock]).begin(); it2 != (m_phiMap[pBlock]).end(); it2++)
                {
                    std::string varAssign = "var__temp_" + (it2->first);
                    llvm::Value *iValue = it2->second;
                    if (iValue->hasName())
                    {
                        valName = getVar(iValue);
                        if (m_t2Output)
                        {
                            std::cout << varAssign << " := " << valName << ";" << std::endl;
                        }
                    }
                    else
                    {
                        if (llvm::isa<llvm::ConstantInt>(iValue))
                        {
                            if (m_boundedIntegers && m_unsignedEncoding)
                            {
                                cv = static_cast<llvm::ConstantInt *>(iValue)->getZExtValue();
                            }
                            else
                            {
                                cv = static_cast<llvm::ConstantInt *>(iValue)->getSExtValue();
                            }
                            if (m_t2Output)
                            {
                                std::cout << varAssign << " := " << cv << ";" << std::endl;
                            }
                        }
                    }
                }

                // for (it2 = (m_phiMap[pBlock]).begin(); it2 != (m_phiMap[pBlock]).end(); it2++)
                // {

                //     std::string varAssign = "var__temp_" + (it2->first);
                //     std::string varOrig = it2->first;

                //     if (m_t2Output)
                //     {
                //         std::cout << varOrig << " := " << varAssign << ";" << std::endl;
                //     }
                // }
            }

            if (branch->isUnconditional())
            {
                //If unconditional then create the condition true
                //Later when visiting terminating transition
                //will print transition from true to BB
                llvm::BasicBlock *iBlock = branch->getSuccessor(0);
                if (m_t2Output)
                {
                    std::cout << "TO: " << (iBlock->getName().str()) << ";" << std::endl;
                }
            }
            else
            {
                //If conditional use condition to transition to block names
                llvm::Value *branchVal = branch->getCondition();
                ref<Constraint> c = getConditionFromValue(branchVal);

                unsigned incomeVals = branch->getNumSuccessors();
                if (incomeVals > 2)
                {
                    std::cerr << "Branching instruction should only ever have two incoming values!" << std::endl;
                    exit(1);
                }

                if (m_t2Output)
                {
                    //Given then we're branching, create an intermediate node to branch through via condition.
                    std::cout << "TO: " << (pBlock->getName().str()) << "_end;" << std::endl
                              << std::endl;

                    //<Negar>
                    //if (c->toT2String() == "nondet()") {
                    //    if (llvm::BranchInst *BI = llvm::dyn_cast<llvm::BranchInst>(&I)) {
                    //        if (BI->isConditional()) {
                    //            std::string varName = BI->getCondition()->getName().str();
                    //
                    //            std::string trueCondition = "v" + varName + " == true";
                    //            std::string trueBlock = branch->getSuccessor(0)->getName().str();
                    //            std::cout << "FROM: " << (pBlock->getName().str()) << "_end;" << std::endl;
                    //            std::cout << "assume(" << trueCondition << ");" << std::endl;
                    //            std::cout << "TO: " << trueBlock << ";" << std::endl << std::endl;
                    //
                    //            std::string falseCondition = "v" + varName + " == false";
                    //            std::string falseBlock = branch->getSuccessor(1)->getName().str();
                    //            std::cout << "FROM: " << (pBlock->getName().str()) << "_end;" << std::endl;
                    //            std::cout << "assume(" << falseCondition << ");" << std::endl;
                    //            std::cout << "TO: " << falseBlock << ";" << std::endl;
                    //        }
                    //    }
                    //}
                    //</Negar>

                    //<Negar>
                    //else {
                    //</Negar>

                        //Transition where the condition holds
                        std::cout << "FROM: " << (pBlock->getName().str()) << "_end;" << std::endl;
                        std::cout << "assume(" << (c->toT2String()) << ");" << std::endl;
                        llvm::BasicBlock *tBlock = branch->getSuccessor(0);
                        std::cout << "TO: " << (tBlock->getName().str()) << ";" << std::endl
                                  << std::endl;

                        //Transition where the condition doesn't hold.
                        std::cout << "FROM: " << (pBlock->getName().str()) << "_end;" << std::endl;
                        std::cout << "assume(" << ((c->toNNF(true))->toT2String()) << ");" << std::endl;
                        llvm::BasicBlock *fBlock = branch->getSuccessor(1);
                        std::cout << "TO: " << (fBlock->getName().str()) << ";" << std::endl;

                    //<Negar>
                    //}
                    //</Negar>
                }
            }
        }
    }
}

void Converter::visitGenericInstruction(llvm::Instruction &I, std::list<ref<Polynomial>> newArgs, ref<Constraint> c)
{
    m_idMap.insert(std::make_pair(&I, m_counter));
    ref<Term> lhs = Term::create(getEval(m_counter), m_lhs);
    ++m_counter;
    ref<Term> rhs = Term::create(getEval(m_counter), newArgs);
    ref<Rule> rule = Rule::create(lhs, rhs, c);
    m_blockRules.push_back(rule);
}

void Converter::visitGenericInstruction(llvm::Instruction &I, ref<Polynomial> value, ref<Constraint> c)
{
    visitGenericInstruction(I, getNewArgs(I, value), c);
}

void Converter::visitAdd(llvm::BinaryOperator &I)
{
    if (I.getType() == m_boolType || I.getType()->isVectorTy())
    {
        return;
    }
    if (m_phase1)
    {
        m_vars.push_back(getVar(&I));
    }
    else
    {
        ref<Polynomial> p1 = getPolynomial(I.getOperand(0));
        ref<Polynomial> p2 = getPolynomial(I.getOperand(1));
        if (m_t2Output)
        {
            std::cout << getVar(&I) << " := " << p1->toString() << " + " << p2->toString() << ";" << std::endl;
        }
        visitGenericInstruction(I, p1->add(p2));
    }
}

void Converter::visitSub(llvm::BinaryOperator &I)
{
    if (I.getType() == m_boolType || I.getType()->isVectorTy())
    {
        return;
    }
    if (m_phase1)
    {
        m_vars.push_back(getVar(&I));
    }
    else
    {
        ref<Polynomial> p1 = getPolynomial(I.getOperand(0));
        ref<Polynomial> p2 = getPolynomial(I.getOperand(1));

        if (m_t2Output)
        {
            std::cout << getVar(&I) << " := " << p1->toString() << " - " << p2->toString() << ";" << std::endl;
        }

        visitGenericInstruction(I, p1->sub(p2));
    }
}

void Converter::visitMul(llvm::BinaryOperator &I)
{
    if (I.getType() == m_boolType || I.getType()->isVectorTy())
    {
        return;
    }
    if (m_phase1)
    {
        m_vars.push_back(getVar(&I));
    }
    else
    {
        ref<Polynomial> p1 = getPolynomial(I.getOperand(0));
        ref<Polynomial> p2 = getPolynomial(I.getOperand(1));

        if (m_t2Output)
        {
            std::cout << getVar(&I) << " := " << p1->toString() << " * " << p2->toString() << ";" << std::endl;

            //<Negar>
            mulInsts.push_back(getVar(&I));
            //</Negar>
        }

        visitGenericInstruction(I, p1->mult(p2));
    }
}

ref<Constraint> Converter::getSDivConstraint(DivConstraintStore &store)
{
    // 1. x = 0 /\ z = 0
    ref<Constraint> case1 = Operator::create(store.xEQnull, store.zEQnull, Operator::And);
    // 2. y = 1 /\ z = x
    ref<Constraint> case2 = Operator::create(store.yEQone, store.zEQx, Operator::And);
    // 3. y = -1 /\ z = -x
    ref<Constraint> case3 = Operator::create(store.yEQnegone, store.zEQnegx, Operator::And);
    // 4. y > 1 /\ x > 0 /\ z >= 0 /\ z < x
    ref<Constraint> case41 = Operator::create(store.yGTRone, store.xGTRnull, Operator::And);
    ref<Constraint> case42 = Operator::create(case41, store.zGEQnull, Operator::And);
    ref<Constraint> case4 = Operator::create(case42, store.zLSSx, Operator::And);
    // 5. y > 1 /\ x < 0 /\ z <= 0 /\ z > x
    ref<Constraint> case51 = Operator::create(store.yGTRone, store.xLSSnull, Operator::And);
    ref<Constraint> case52 = Operator::create(case51, store.zLEQnull, Operator::And);
    ref<Constraint> case5 = Operator::create(case52, store.zGTRx, Operator::And);
    // 6. y < -1 /\ x > 0 /\ z <= 0 /\ z > -x
    ref<Constraint> case61 = Operator::create(store.yLSSnegone, store.xGTRnull, Operator::And);
    ref<Constraint> case62 = Operator::create(case61, store.zLEQnull, Operator::And);
    ref<Constraint> case6 = Operator::create(case62, store.zGTRnegx, Operator::And);
    // 7. y < -1 /\ x < 0 /\ z >= 0 /\ z < -x
    ref<Constraint> case71 = Operator::create(store.yLSSnegone, store.xLSSnull, Operator::And);
    ref<Constraint> case72 = Operator::create(case71, store.zGEQnull, Operator::And);
    ref<Constraint> case7 = Operator::create(case72, store.zLSSnegx, Operator::And);
    // disjunct...
    ref<Constraint> disj = Operator::create(case1, case2, Operator::Or);
    disj = Operator::create(disj, case3, Operator::Or);
    disj = Operator::create(disj, case4, Operator::Or);
    disj = Operator::create(disj, case5, Operator::Or);
    disj = Operator::create(disj, case6, Operator::Or);
    disj = Operator::create(disj, case7, Operator::Or);
    return disj;
}

ref<Constraint> Converter::getSDivConstraintForUnbounded(ref<Polynomial> upper, ref<Polynomial> lower, ref<Polynomial> res)
{
    ref<Polynomial> null = Polynomial::null;
    ref<Polynomial> one = Polynomial::one;
    ref<Polynomial> negone = Polynomial::negone;
    ref<Polynomial> negupper = upper->constMult(Polynomial::_negone);

    ref<Polynomial> x = upper;
    ref<Polynomial> y = lower;
    ref<Polynomial> z = res;
    ref<Polynomial> negx = negupper;

    DivConstraintStore store;

    store.xEQnull = Atom::create(x, null, Atom::Equ);
    store.yEQone = Atom::create(y, one, Atom::Equ);
    store.yEQnegone = Atom::create(y, negone, Atom::Equ);
    store.zEQnull = Atom::create(z, null, Atom::Equ);
    store.zEQx = Atom::create(z, x, Atom::Equ);
    store.zEQnegx = Atom::create(z, negx, Atom::Equ);
    //<Negar>
    if (signednessInfo) {
        store.yGTRone = Atom::create(y, one, Atom::Sgt);
        store.xGTRnull = Atom::create(x, null, Atom::Sgt);
        store.zGEQnull = Atom::create(z, null, Atom::Sge);
        store.zLSSx = Atom::create(z, x, Atom::Slt);
        store.xLSSnull = Atom::create(x, null, Atom::Slt);
        store.zLEQnull = Atom::create(z, null, Atom::Sle);
        store.zGTRx = Atom::create(z, x, Atom::Sgt);
        store.yLSSnegone = Atom::create(y, negone, Atom::Slt);
        store.zGTRnegx = Atom::create(z, negx, Atom::Sgt);
        store.zLSSnegx = Atom::create(z, negx, Atom::Slt);
    }
    else {
        store.yGTRone = Atom::create(y, one, Atom::Gtr);
        store.xGTRnull = Atom::create(x, null, Atom::Gtr);
        store.zGEQnull = Atom::create(z, null, Atom::Geq);
        store.zLSSx = Atom::create(z, x, Atom::Lss);
        store.xLSSnull = Atom::create(x, null, Atom::Lss);
        store.zLEQnull = Atom::create(z, null, Atom::Leq);
        store.zGTRx = Atom::create(z, x, Atom::Gtr);
        store.yLSSnegone = Atom::create(y, negone, Atom::Lss);
        store.zGTRnegx = Atom::create(z, negx, Atom::Gtr);
        store.zLSSnegx = Atom::create(z, negx, Atom::Lss);
    }
    //</Negar>

    return getSDivConstraint(store);
}

ref<Constraint> Converter::getSDivConstraintForSignedBounded(ref<Polynomial> upper, ref<Polynomial> lower, ref<Polynomial> res)
{
    return getSDivConstraintForUnbounded(upper, lower, res);
}

ref<Constraint> Converter::getSDivConstraintForUnsignedBounded(ref<Polynomial> upper, ref<Polynomial> lower, ref<Polynomial> res, unsigned int bitwidth)
{
    ref<Polynomial> null = Polynomial::null;
    ref<Polynomial> one = Polynomial::one;
    ref<Polynomial> negone = Polynomial::uimax(bitwidth);
    ref<Polynomial> maxpos = Polynomial::simax(bitwidth);
    ref<Polynomial> minneg = Polynomial::simin_as_ui(bitwidth);
    ref<Polynomial> negupper = upper->constMult(Polynomial::_negone);

    ref<Polynomial> x = upper;
    ref<Polynomial> y = lower;
    ref<Polynomial> z = res;
    ref<Polynomial> negx = negupper;

    DivConstraintStore store;

    store.xEQnull = Atom::create(x, null, Atom::Equ);
    store.yEQone = Atom::create(y, one, Atom::Equ);
    store.yEQnegone = Atom::create(y, negone, Atom::Equ);
    store.zEQnull = Atom::create(z, null, Atom::Equ);
    store.zEQx = Atom::create(z, x, Atom::Equ);
    store.zEQnegx = Atom::create(z, negx, Atom::Equ);
    //<Negar>
    ref<Constraint> yGTRone1;
    ref<Constraint> yGTRone2;
    if (signednessInfo) {
        yGTRone1 = Atom::create(y, one, Atom::Sgt);
        yGTRone2 = Atom::create(y, maxpos, Atom::Sle);
    }
    else {
        yGTRone1 = Atom::create(y, one, Atom::Gtr);
        yGTRone2 = Atom::create(y, maxpos, Atom::Leq);
    }
    //</Negar>
    store.yGTRone = Operator::create(yGTRone1, yGTRone2, Operator::And);
    //<Negar>
    ref<Constraint> xGTRnull1;
    ref<Constraint> xGTRnull2;
    if (signednessInfo) {
        xGTRnull1 = Atom::create(x, null, Atom::Sgt);
        xGTRnull2 = Atom::create(x, maxpos, Atom::Sle);
    }
    else {
        xGTRnull1 = Atom::create(x, null, Atom::Gtr);
        xGTRnull2 = Atom::create(x, maxpos, Atom::Leq);
    }
    //</Negar>
    store.xGTRnull = Operator::create(xGTRnull1, xGTRnull2, Operator::And);
    //<Negar>
    if (signednessInfo) {
        store.zGEQnull = Atom::create(z, maxpos, Atom::Sle);
    }
    else {
        store.zGEQnull = Atom::create(z, maxpos, Atom::Leq);
    }
    //</Negar>
    store.zLSSx = getSignedComparisonForUnsignedBounded(llvm::CmpInst::ICMP_SLT, z, x, bitwidth);
    //<Negar>
    ref<Constraint> zLEQnull1;
    if (signednessInfo) {
        store.xLSSnull = Atom::create(x, minneg, Atom::Sge);
        zLEQnull1 = Atom::create(z, minneg, Atom::Sge);
    }
    else {
        store.xLSSnull = Atom::create(x, minneg, Atom::Geq);
        zLEQnull1 = Atom::create(z, minneg, Atom::Geq);
    }
    //</Negar>
    ref<Constraint> zLEQnull2 = Atom::create(z, null, Atom::Equ);
    store.zLEQnull = Operator::create(zLEQnull1, zLEQnull2, Operator::Or);
    store.zGTRx = getSignedComparisonForUnsignedBounded(llvm::CmpInst::ICMP_SGT, z, x, bitwidth);
    //<Negar>
    ref<Constraint> yLSSnegone1;
    ref<Constraint> yLSSnegone2;
    if (signednessInfo) {
        yLSSnegone1 = Atom::create(y, minneg, Atom::Sge);
        yLSSnegone2 = Atom::create(y, negone, Atom::Slt);
    }
    else {
        yLSSnegone1 = Atom::create(y, minneg, Atom::Geq);
        yLSSnegone2 = Atom::create(y, negone, Atom::Lss);
    }
    //</Negar>
    store.yLSSnegone = Operator::create(yLSSnegone1, yLSSnegone2, Operator::And);
    store.zGTRnegx = getSignedComparisonForUnsignedBounded(llvm::CmpInst::ICMP_SGT, z, negx, bitwidth);
    store.zLSSnegx = getSignedComparisonForUnsignedBounded(llvm::CmpInst::ICMP_SLT, z, negx, bitwidth);

    return getSDivConstraint(store);
}

ref<Constraint> Converter::getExactSDivConstraintForUnbounded(ref<Polynomial> upper, ref<Polynomial> lower, ref<Polynomial> res)
{
    // x/y = z
    ref<Polynomial> px = upper;
    ref<Polynomial> py = lower;
    ref<Polynomial> pz = res;
    ref<Polynomial> pnegx = px->constMult(Polynomial::_negone);
    ref<Polynomial> pnegy = py->constMult(Polynomial::_negone);
    ref<Polynomial> pnull = Polynomial::null;
    // 1. x = 0 /\ z = 0
    ref<Constraint> pxnull = Atom::create(px, pnull, Atom::Equ);
    ref<Constraint> pznull = Atom::create(pz, pnull, Atom::Equ);
    ref<Constraint> case1 = Operator::create(pxnull, pznull, Operator::And);
    // 2. y > 0 /\ x > 0 /\ z >= 0 /\ x - y*z >= 0 /\ x - y*z < y
    //<Negar>
    ref<Constraint> pygtrnull;
    ref<Constraint> pxgtrnull;
    ref<Constraint> pzgeqnull;
    if (signednessInfo) {
        pygtrnull = Atom::create(py, pnull, Atom::Sgt);
        pxgtrnull = Atom::create(px, pnull, Atom::Sgt);
        pzgeqnull = Atom::create(pz, pnull, Atom::Sge);
    }
    else {
        pygtrnull = Atom::create(py, pnull, Atom::Gtr);
        pxgtrnull = Atom::create(px, pnull, Atom::Gtr);
        pzgeqnull = Atom::create(pz, pnull, Atom::Geq);
    }
    //</Negar>
    ref<Polynomial> term2 = px->sub(py->mult(pz));
    //<Negar>
    ref<Constraint> term2geqnull;
    ref<Constraint> term2lssy;
    if (signednessInfo) {
        term2geqnull = Atom::create(term2, pnull, Atom::Sge);
        term2lssy = Atom::create(term2, py, Atom::Slt);
    }
    else {
        term2geqnull = Atom::create(term2, pnull, Atom::Geq);
        term2lssy = Atom::create(term2, py, Atom::Lss);
    }
    //</Negar>
    ref<Constraint> case21 = Operator::create(pygtrnull, pxgtrnull, Operator::And);
    ref<Constraint> case22 = Operator::create(case21, pzgeqnull, Operator::And);
    ref<Constraint> case23 = Operator::create(case22, term2geqnull, Operator::And);
    ref<Constraint> case2 = Operator::create(case23, term2lssy, Operator::And);
    // 3. y < 0 /\ x > 0 /\ z <= 0 /\ x - y*z >= 0 /\ x - y*z < -y
    //<Negar>
    ref<Constraint> pylssnull;
    ref<Constraint> pzleqnull;
    ref<Constraint> term2lssnegy;
    if (signednessInfo) {
        pylssnull = Atom::create(py, pnull, Atom::Slt);
        pzleqnull = Atom::create(pz, pnull, Atom::Sle);
        term2lssnegy = Atom::create(term2, pnegy, Atom::Slt);
    }
    else {
        pylssnull = Atom::create(py, pnull, Atom::Lss);
        pzleqnull = Atom::create(pz, pnull, Atom::Leq);
        term2lssnegy = Atom::create(term2, pnegy, Atom::Lss);
    }
    //</Negar>
    ref<Constraint> case31 = Operator::create(pylssnull, pxgtrnull, Operator::And);
    ref<Constraint> case32 = Operator::create(case31, pzleqnull, Operator::And);
    ref<Constraint> case33 = Operator::create(case32, term2geqnull, Operator::And);
    ref<Constraint> case3 = Operator::create(case33, term2lssnegy, Operator::And);
    // 4. y > 0 /\ x < 0 /\ z <= 0 /\ -x + y*z >= 0 /\ -x + y*z < y
    //<Negar>
    ref<Constraint> pxlssnull;
    if (signednessInfo) {
        pxlssnull = Atom::create(px, pnull, Atom::Slt);
    }
    else {
        pxlssnull = Atom::create(px, pnull, Atom::Lss);
    }
    //</Negar>
    ref<Polynomial> term4 = pnegx->add(py->mult(pz));
    //<Negar>
    ref<Constraint> term4geqnull;
    ref<Constraint> term4lssy;
    if (signednessInfo) {
        term4geqnull = Atom::create(term4, pnull, Atom::Sge);
        term4lssy = Atom::create(term4, py, Atom::Slt);
    }
    else {
        term4geqnull = Atom::create(term4, pnull, Atom::Geq);
        term4lssy = Atom::create(term4, py, Atom::Lss);
    }
    //</Negar>
    ref<Constraint> case41 = Operator::create(pygtrnull, pxlssnull, Operator::And);
    ref<Constraint> case42 = Operator::create(case41, pzleqnull, Operator::And);
    ref<Constraint> case43 = Operator::create(case42, term4geqnull, Operator::And);
    ref<Constraint> case4 = Operator::create(case43, term4lssy, Operator::And);
    // 5. y < 0 /\ x < 0 /\ z >= 0 /\ -x + y*z >= 0 /\ -x + y*z < -y
    //<Negar>
    ref<Constraint> term4lssnegy;
    if (signednessInfo) {
        term4lssnegy = Atom::create(term4, pnegy, Atom::Slt);
    }
    else {
        term4lssnegy = Atom::create(term4, pnegy, Atom::Lss);
    }
    //</Negar>
    ref<Constraint> case51 = Operator::create(pylssnull, pxlssnull, Operator::And);
    ref<Constraint> case52 = Operator::create(case51, pzgeqnull, Operator::And);
    ref<Constraint> case53 = Operator::create(case52, term4geqnull, Operator::And);
    ref<Constraint> case5 = Operator::create(case53, term4lssnegy, Operator::And);
    // disjunct...
    ref<Constraint> disj = Operator::create(case1, case2, Operator::Or);
    disj = Operator::create(disj, case3, Operator::Or);
    disj = Operator::create(disj, case4, Operator::Or);
    disj = Operator::create(disj, case5, Operator::Or);
    return disj;
}

void Converter::visitSDiv(llvm::BinaryOperator &I)
{
    if (I.getType() == m_boolType || I.getType()->isVectorTy())
    {
        return;
    }
    if (m_phase1)
    {
        m_vars.push_back(getVar(&I));
    }
    else
    {
        ref<Polynomial> nondef = Polynomial::create(getNondef(&I));
        ref<Constraint> divC;
        ref<Polynomial> upper = getPolynomial(I.getOperand(0));
        ref<Polynomial> lower = getPolynomial(I.getOperand(1));
        if (m_divisionConstraintType != None)
        {
            if (m_boundedIntegers)
            {
                unsigned int bitwidth = llvm::cast<llvm::IntegerType>(I.getType())->getBitWidth();
                divC = m_unsignedEncoding ? getSDivConstraintForUnsignedBounded(upper, lower, nondef, bitwidth) : getSDivConstraintForSignedBounded(upper, lower, nondef);
            }
            else
            {
                divC = (m_divisionConstraintType == Exact) ? getExactSDivConstraintForUnbounded(upper, lower, nondef) : getSDivConstraintForUnbounded(upper, lower, nondef);
            }
        }
        else
        {
            divC = Constraint::_true;
        }
        if (m_t2Output)
        {
            //<Negar>
            if (signednessInfo) {
                std::cout << getVar(&I) << " := " << upper->toString() << " sdiv " << lower->toString() << ";" << std::endl;
            }
            else {
                std::cout << getVar(&I) << " := " << upper->toString() << " / " << lower->toString() << ";" << std::endl;
            }
            //</Negar>
        }
        visitGenericInstruction(I, nondef, divC);
    }
}

ref<Constraint> Converter::getUDivConstraint(DivConstraintStore &store)
{
    // 1. x = 0 /\ z = 0
    ref<Constraint> case1 = Operator::create(store.xEQnull, store.zEQnull, Operator::And);
    // 2. y = 1 /\ z = x
    ref<Constraint> case2 = Operator::create(store.yEQone, store.zEQx, Operator::And);
    // 3. y > 1 /\ x > 0 /\ z < x
    ref<Constraint> case31 = Operator::create(store.yGTRone, store.xGTRnull, Operator::And);
    ref<Constraint> case3 = Operator::create(case31, store.zLSSx, Operator::And);
    // disjunct...
    ref<Constraint> disj = Operator::create(case1, case2, Operator::Or);
    disj = Operator::create(disj, case3, Operator::Or);
    return disj;
}

ref<Constraint> Converter::getUDivConstraintForUnbounded(ref<Polynomial> upper, ref<Polynomial> lower, ref<Polynomial> res)
{
    return getSDivConstraintForUnbounded(upper, lower, res);
}

ref<Constraint> Converter::getUDivConstraintForSignedBounded(ref<Polynomial> upper, ref<Polynomial> lower, ref<Polynomial> res)
{
    ref<Polynomial> null = Polynomial::null;
    ref<Polynomial> one = Polynomial::one;

    ref<Polynomial> x = upper;
    ref<Polynomial> y = lower;
    ref<Polynomial> z = res;

    DivConstraintStore store;

    store.xEQnull = Atom::create(x, null, Atom::Equ);
    store.yEQone = Atom::create(y, one, Atom::Equ);
    store.zEQnull = Atom::create(z, null, Atom::Equ);
    store.zEQx = Atom::create(z, x, Atom::Equ);
    //<Negar>
    ref<Constraint> yGTRone1;
    ref<Constraint> yGTRone2;
    if (signednessInfo) {
        yGTRone1 = Atom::create(y, one, Atom::Ugt);
        yGTRone2 = Atom::create(y, null, Atom::Ult);
    }
    else {
        yGTRone1 = Atom::create(y, one, Atom::Gtr);
        yGTRone2 = Atom::create(y, null, Atom::Lss);
    }
    //</Negar>
    store.yGTRone = Operator::create(yGTRone1, yGTRone2, Operator::Or);
    //<Negar>
    ref<Constraint> xGTRnull1;
    ref<Constraint> xGTRnull2;
    if (signednessInfo) {
        xGTRnull1 = Atom::create(x, null, Atom::Ugt);
        xGTRnull2 = Atom::create(x, null, Atom::Ult);
    }
    else {
        xGTRnull1 = Atom::create(x, null, Atom::Gtr);
        xGTRnull2 = Atom::create(x, null, Atom::Lss);
    }
    //</Negar>
    store.xGTRnull = Operator::create(xGTRnull1, xGTRnull2, Operator::Or);
    store.zLSSx = getUnsignedComparisonForSignedBounded(llvm::CmpInst::ICMP_ULT, z, x);

    return getUDivConstraint(store);
}

ref<Constraint> Converter::getUDivConstraintForUnsignedBounded(ref<Polynomial> upper, ref<Polynomial> lower, ref<Polynomial> res)
{
    ref<Polynomial> null = Polynomial::null;
    ref<Polynomial> one = Polynomial::one;

    ref<Polynomial> x = upper;
    ref<Polynomial> y = lower;
    ref<Polynomial> z = res;

    DivConstraintStore store;

    store.xEQnull = Atom::create(x, null, Atom::Equ);
    store.yEQone = Atom::create(y, one, Atom::Equ);
    store.zEQnull = Atom::create(z, null, Atom::Equ);
    store.zEQx = Atom::create(z, x, Atom::Equ);
    //<Negar>
    if (signednessInfo) {
        store.yGTRone = Atom::create(y, one, Atom::Ugt);
        store.xGTRnull = Atom::create(x, null, Atom::Ugt);
        store.zLSSx = Atom::create(z, x, Atom::Ult);
    }
    else {
        store.yGTRone = Atom::create(y, one, Atom::Gtr);
        store.xGTRnull = Atom::create(x, null, Atom::Gtr);
        store.zLSSx = Atom::create(z, x, Atom::Lss);
    }
    //</Negar>

    return getUDivConstraint(store);
}

ref<Constraint> Converter::getExactUDivConstraintForUnbounded(ref<Polynomial> upper, ref<Polynomial> lower, ref<Polynomial> res)
{
    return getExactSDivConstraintForUnbounded(upper, lower, res);
}

void Converter::visitUDiv(llvm::BinaryOperator &I)
{
    if (I.getType() == m_boolType || I.getType()->isVectorTy())
    {
        return;
    }
    if (m_phase1)
    {
        m_vars.push_back(getVar(&I));
    }
    else
    {
        ref<Polynomial> nondef = Polynomial::create(getNondef(&I));
        ref<Constraint> divC;
        ref<Polynomial> upper = getPolynomial(I.getOperand(0));
        ref<Polynomial> lower = getPolynomial(I.getOperand(1));
        if (m_divisionConstraintType != None)
        {
            if (m_boundedIntegers)
            {
                divC = m_unsignedEncoding ? getUDivConstraintForUnsignedBounded(upper, lower, nondef) : getUDivConstraintForSignedBounded(upper, lower, nondef);
            }
            else
            {
                divC = (m_divisionConstraintType == Exact) ? getExactUDivConstraintForUnbounded(upper, lower, nondef) : getUDivConstraintForUnbounded(upper, lower, nondef);
            }
        }
        else
        {
            divC = Constraint::_true;
        }
        if (m_t2Output)
        {
            //<Negar>
            if (signednessInfo) {
                std::cout << getVar(&I) << " := " << upper->toString() << " udiv " << lower->toString() << ";" << std::endl;
            }
            else {
                std::cout << getVar(&I) << " := " << upper->toString() << " / " << lower->toString() << ";" << std::endl;
            }
            //</Negar>
        }
        visitGenericInstruction(I, nondef, divC);
    }
}

ref<Constraint> Converter::getSRemConstraint(RemConstraintStore &store)
{
    // 1. x = 0 /\ z = 0
    ref<Constraint> case1 = Operator::create(store.xEQnull, store.zEQnull, Operator::And);
    // 2. y = 1 /\ z = 0
    ref<Constraint> case2 = Operator::create(store.yEQone, store.zEQnull, Operator::And);
    // 3. y = -1 /\ z = 0
    ref<Constraint> case3 = Operator::create(store.yEQnegone, store.zEQnull, Operator::And);
    // 4. y > 1 /\ x > 0 /\ z >= 0 /\ z < y
    ref<Constraint> case41 = Operator::create(store.yGTRone, store.xGTRnull, Operator::And);
    ref<Constraint> case42 = Operator::create(case41, store.zGEQnull, Operator::And);
    ref<Constraint> case4 = Operator::create(case42, store.zLSSy, Operator::And);
    // 5. y > 1 /\ x < 0 /\ z <= 0 /\ z > -y
    ref<Constraint> case51 = Operator::create(store.yGTRone, store.xLSSnull, Operator::And);
    ref<Constraint> case52 = Operator::create(case51, store.zLEQnull, Operator::And);
    ref<Constraint> case5 = Operator::create(case52, store.zGTRnegy, Operator::And);
    // 6. y < -1 /\ x > 0 /\ z >= 0 /\ z < -y
    ref<Constraint> case61 = Operator::create(store.yLSSnegone, store.xGTRnull, Operator::And);
    ref<Constraint> case62 = Operator::create(case61, store.zGEQnull, Operator::And);
    ref<Constraint> case6 = Operator::create(case62, store.zLSSnegy, Operator::And);
    // 7. y < -1 /\ x < 0 /\ z <= 0 /\ z > y
    ref<Constraint> case71 = Operator::create(store.yLSSnegone, store.xLSSnull, Operator::And);
    ref<Constraint> case72 = Operator::create(case71, store.zLEQnull, Operator::And);
    ref<Constraint> case7 = Operator::create(case72, store.zGTRy, Operator::And);
    // disjunct...
    ref<Constraint> disj = Operator::create(case1, case2, Operator::Or);
    disj = Operator::create(disj, case3, Operator::Or);
    disj = Operator::create(disj, case4, Operator::Or);
    disj = Operator::create(disj, case5, Operator::Or);
    disj = Operator::create(disj, case6, Operator::Or);
    disj = Operator::create(disj, case7, Operator::Or);
    return disj;
}

ref<Constraint> Converter::getSRemConstraintForUnbounded(ref<Polynomial> upper, ref<Polynomial> lower, ref<Polynomial> res)
{
    ref<Polynomial> null = Polynomial::null;
    ref<Polynomial> one = Polynomial::one;
    ref<Polynomial> negone = Polynomial::negone;
    ref<Polynomial> neglower = lower->constMult(Polynomial::_negone);

    ref<Polynomial> x = upper;
    ref<Polynomial> y = lower;
    ref<Polynomial> z = res;
    ref<Polynomial> negy = neglower;

    RemConstraintStore store;

    store.xEQnull = Atom::create(x, null, Atom::Equ);
    store.zEQnull = Atom::create(z, null, Atom::Equ);
    store.yEQone = Atom::create(y, one, Atom::Equ);
    store.yEQnegone = Atom::create(y, negone, Atom::Equ);
    //<Negar>
    if (signednessInfo) {
        store.yGTRone = Atom::create(y, one, Atom::Sgt);
        store.xGTRnull = Atom::create(x, null, Atom::Sgt);
        store.zGEQnull = Atom::create(z, null, Atom::Sge);
        store.zLSSy = Atom::create(z, y, Atom::Slt);
        store.xLSSnull = Atom::create(x, null, Atom::Slt);
        store.zLEQnull = Atom::create(z, null, Atom::Sle);
        store.zGTRnegy = Atom::create(z, negy, Atom::Sgt);
        store.yLSSnegone = Atom::create(y, negone, Atom::Slt);
        store.zLSSnegy = Atom::create(z, negy, Atom::Slt);
        store.zGTRy = Atom::create(z, y, Atom::Sgt);
    }
    else {
        store.yGTRone = Atom::create(y, one, Atom::Gtr);
        store.xGTRnull = Atom::create(x, null, Atom::Gtr);
        store.zGEQnull = Atom::create(z, null, Atom::Geq);
        store.zLSSy = Atom::create(z, y, Atom::Lss);
        store.xLSSnull = Atom::create(x, null, Atom::Lss);
        store.zLEQnull = Atom::create(z, null, Atom::Leq);
        store.zGTRnegy = Atom::create(z, negy, Atom::Gtr);
        store.yLSSnegone = Atom::create(y, negone, Atom::Lss);
        store.zLSSnegy = Atom::create(z, negy, Atom::Lss);
        store.zGTRy = Atom::create(z, y, Atom::Gtr);
    }
    //</Negar>

    return getSRemConstraint(store);
}

ref<Constraint> Converter::getSRemConstraintForSignedBounded(ref<Polynomial> upper, ref<Polynomial> lower, ref<Polynomial> res)
{
    return getSRemConstraintForUnbounded(upper, lower, res);
}

ref<Constraint> Converter::getSRemConstraintForUnsignedBounded(ref<Polynomial> upper, ref<Polynomial> lower, ref<Polynomial> res, unsigned int bitwidth)
{
    ref<Polynomial> null = Polynomial::null;
    ref<Polynomial> one = Polynomial::one;
    ref<Polynomial> negone = Polynomial::uimax(bitwidth);
    ref<Polynomial> maxpos = Polynomial::simax(bitwidth);
    ref<Polynomial> minneg = Polynomial::simin_as_ui(bitwidth);
    ref<Polynomial> neglower = lower->constMult(Polynomial::_negone);

    ref<Polynomial> x = upper;
    ref<Polynomial> y = lower;
    ref<Polynomial> z = res;
    ref<Polynomial> negy = neglower;

    RemConstraintStore store;

    store.xEQnull = Atom::create(x, null, Atom::Equ);
    store.zEQnull = Atom::create(z, null, Atom::Equ);
    store.yEQone = Atom::create(y, one, Atom::Equ);
    store.yEQnegone = Atom::create(y, negone, Atom::Equ);
    //<Negar>
    ref<Constraint> yGTRone1;
    ref<Constraint> yGTRone2;
    if (signednessInfo) {
        yGTRone1 = Atom::create(y, one, Atom::Sgt);
        yGTRone2 = Atom::create(y, maxpos, Atom::Sle);
    }
    else {
        yGTRone1 = Atom::create(y, one, Atom::Gtr);
        yGTRone2 = Atom::create(y, maxpos, Atom::Leq);
    }
    //</Negar>
    store.yGTRone = Operator::create(yGTRone1, yGTRone2, Operator::And);
    //<Negar>
    ref<Constraint> xGTRnull1;
    ref<Constraint> xGTRnull2;
    if (signednessInfo) {
        xGTRnull1 = Atom::create(x, null, Atom::Sgt);
        xGTRnull2 = Atom::create(x, maxpos, Atom::Sle);
    }
    else {
        xGTRnull1 = Atom::create(x, null, Atom::Gtr);
        xGTRnull2 = Atom::create(x, maxpos, Atom::Leq);
    }
    //</Negar>
    store.xGTRnull = Operator::create(xGTRnull1, xGTRnull2, Operator::And);
    //<Negar>
    if (signednessInfo) {
        store.zGEQnull = Atom::create(z, maxpos, Atom::Sle);
    }
    else {
        store.zGEQnull = Atom::create(z, maxpos, Atom::Leq);
    }
    //</Negar>
    store.zLSSy = getSignedComparisonForUnsignedBounded(llvm::CmpInst::ICMP_SLT, z, y, bitwidth);
    //<Negar>
    ref<Constraint> zLEQnull1;
    if (signednessInfo) {
        store.xLSSnull = Atom::create(x, minneg, Atom::Sge);
        zLEQnull1 = Atom::create(z, minneg, Atom::Sge);
    }
    else {
        store.xLSSnull = Atom::create(x, minneg, Atom::Geq);
        zLEQnull1 = Atom::create(z, minneg, Atom::Geq);
    }
    //</Negar>
    ref<Constraint> zLEQnull2 = Atom::create(z, null, Atom::Equ);
    store.zLEQnull = Operator::create(zLEQnull1, zLEQnull2, Operator::Or);
    store.zGTRnegy = getSignedComparisonForUnsignedBounded(llvm::CmpInst::ICMP_SGT, z, negy, bitwidth);
    //<Negar>
    ref<Constraint> yLSSnegone1;
    ref<Constraint> yLSSnegone2;
    if (signednessInfo) {
        yLSSnegone1 = Atom::create(y, minneg, Atom::Sge);
        yLSSnegone2 = Atom::create(y, negone, Atom::Slt);
    }
    else {
        yLSSnegone1 = Atom::create(y, minneg, Atom::Geq);
        yLSSnegone2 = Atom::create(y, negone, Atom::Lss);
    }
    //</Negar>
    store.yLSSnegone = Operator::create(yLSSnegone1, yLSSnegone2, Operator::And);
    store.zLSSnegy = getSignedComparisonForUnsignedBounded(llvm::CmpInst::ICMP_SLT, z, negy, bitwidth);
    store.zGTRy = getSignedComparisonForUnsignedBounded(llvm::CmpInst::ICMP_SGT, z, y, bitwidth);

    ref<Constraint> ret = getSRemConstraint(store);
    return ret;
}

void Converter::visitSRem(llvm::BinaryOperator &I)
{
    if (I.getType() == m_boolType)
    {
        return;
    }
    if (m_phase1)
    {
        m_vars.push_back(getVar(&I));
    }
    else
    {
        ref<Polynomial> nondef = Polynomial::create(getNondef(&I));
        ref<Constraint> remC;
        ref<Polynomial> upper = getPolynomial(I.getOperand(0));
        ref<Polynomial> lower = getPolynomial(I.getOperand(1));
        if (m_divisionConstraintType != None)
        {
            if (m_boundedIntegers)
            {
                unsigned int bitwidth = llvm::cast<llvm::IntegerType>(I.getType())->getBitWidth();
                remC = m_unsignedEncoding ? getSRemConstraintForUnsignedBounded(upper, lower, nondef, bitwidth) : getSRemConstraintForSignedBounded(upper, lower, nondef);
            }
            else
            {
                remC = getSRemConstraintForUnbounded(upper, lower, nondef);
            }
        }
        else
        {
            remC = Constraint::_true;
        }
        if (m_t2Output)
        {
            //<Negar>
            if (signednessInfo) {
                std::cout << getVar(&I) << " := " << upper->toString() << " srem " << lower->toString() << ";" << std::endl;
            }
            else {
                std::cout << getVar(&I) << " := " << upper->toString() << " % " << lower->toString() << ";" << std::endl;
            }
            //</Negar>
        }
        visitGenericInstruction(I, nondef, remC);
    }
}

ref<Constraint> Converter::getURemConstraint(RemConstraintStore &store)
{
    // 1. x = 0 /\ z = 0
    ref<Constraint> case1 = Operator::create(store.xEQnull, store.zEQnull, Operator::And);
    // 2. y = 1 /\ z = 0
    ref<Constraint> case2 = Operator::create(store.yEQone, store.zEQnull, Operator::And);
    // 3. y > 1 /\ x > 0 /\ z < y
    ref<Constraint> case31 = Operator::create(store.yGTRone, store.xGTRnull, Operator::And);
    ref<Constraint> case3 = Operator::create(case31, store.zLSSy, Operator::And);
    // disjunct...
    ref<Constraint> disj = Operator::create(case1, case2, Operator::Or);
    disj = Operator::create(disj, case3, Operator::Or);
    return disj;
}

ref<Constraint> Converter::getURemConstraintForUnbounded(ref<Polynomial> upper, ref<Polynomial> lower, ref<Polynomial> res)
{
    return getSRemConstraintForUnbounded(upper, lower, res);
}

ref<Constraint> Converter::getURemConstraintForSignedBounded(ref<Polynomial> upper, ref<Polynomial> lower, ref<Polynomial> res)
{
    ref<Polynomial> null = Polynomial::null;
    ref<Polynomial> one = Polynomial::one;

    ref<Polynomial> x = upper;
    ref<Polynomial> y = lower;
    ref<Polynomial> z = res;

    RemConstraintStore store;

    store.xEQnull = Atom::create(x, null, Atom::Equ);
    store.zEQnull = Atom::create(z, null, Atom::Equ);
    store.yEQone = Atom::create(y, one, Atom::Equ);
    //<Negar>
    ref<Constraint> yGTRone1;
    ref<Constraint> yGTRone2;
    if (signednessInfo) {
        yGTRone1 = Atom::create(y, one, Atom::Ugt);
        yGTRone2 = Atom::create(y, null, Atom::Ult);
    }
    else {
        yGTRone1 = Atom::create(y, one, Atom::Gtr);
        yGTRone2 = Atom::create(y, null, Atom::Lss);
    }
    //</Negar>
    store.yGTRone = Operator::create(yGTRone1, yGTRone2, Operator::Or);
    //<Negar>
    ref<Constraint> xGTRnull1;
    ref<Constraint> xGTRnull2;
    if (signednessInfo) {
        xGTRnull1 = Atom::create(x, null, Atom::Ugt);
        xGTRnull2 = Atom::create(x, null, Atom::Ult);
    }
    else {
        xGTRnull1 = Atom::create(x, null, Atom::Gtr);
        xGTRnull2 = Atom::create(x, null, Atom::Lss);
    }
    //</Negar>
    store.xGTRnull = Operator::create(xGTRnull1, xGTRnull2, Operator::Or);
    store.zLSSy = getUnsignedComparisonForSignedBounded(llvm::CmpInst::ICMP_ULT, z, y);

    return getURemConstraint(store);
}

ref<Constraint> Converter::getURemConstraintForUnsignedBounded(ref<Polynomial> upper, ref<Polynomial> lower, ref<Polynomial> res)
{
    ref<Polynomial> null = Polynomial::null;
    ref<Polynomial> one = Polynomial::one;

    ref<Polynomial> x = upper;
    ref<Polynomial> y = lower;
    ref<Polynomial> z = res;

    RemConstraintStore store;

    store.xEQnull = Atom::create(x, null, Atom::Equ);
    store.zEQnull = Atom::create(z, null, Atom::Equ);
    store.yEQone = Atom::create(y, one, Atom::Equ);
    //<Negar>
    if (signednessInfo) {
        store.yGTRone = Atom::create(y, one, Atom::Ugt);
        store.xGTRnull = Atom::create(x, null, Atom::Ugt);
        store.zLSSy = Atom::create(z, y, Atom::Ult);
    }
    else {
        store.yGTRone = Atom::create(y, one, Atom::Gtr);
        store.xGTRnull = Atom::create(x, null, Atom::Gtr);
        store.zLSSy = Atom::create(z, y, Atom::Lss);
    }
    //</Negar>

    return getURemConstraint(store);
}

void Converter::visitURem(llvm::BinaryOperator &I)
{
    if (I.getType() == m_boolType)
    {
        return;
    }
    if (m_phase1)
    {
        m_vars.push_back(getVar(&I));
    }
    else
    {
        ref<Polynomial> nondef = Polynomial::create(getNondef(&I));
        ref<Constraint> remC;
        ref<Polynomial> upper = getPolynomial(I.getOperand(0));
        ref<Polynomial> lower = getPolynomial(I.getOperand(1));
        if (m_divisionConstraintType != None)
        {
            if (m_boundedIntegers)
            {
                remC = m_unsignedEncoding ? getURemConstraintForUnsignedBounded(upper, lower, nondef) : getURemConstraintForSignedBounded(upper, lower, nondef);
            }
            else
            {
                remC = getURemConstraintForUnbounded(upper, lower, nondef);
            }
        }
        else
        {
            remC = Constraint::_true;
        }
        if (m_t2Output)
        {
            //<Negar>
            if (signednessInfo) {
                std::cout << getVar(&I) << " := " << upper->toString() << " urem " << lower->toString() << ";" << std::endl;
            }
            else {
                std::cout << getVar(&I) << " := " << upper->toString() << " % " << lower->toString() << ";" << std::endl;
            }
            //</Negar>
        }
        visitGenericInstruction(I, nondef, remC);
    }
}

ref<Constraint> Converter::getAndConstraintForBounded(ref<Polynomial> x, ref<Polynomial> y, ref<Polynomial> res)
{
    //<Negar>
    ref<Constraint> resLEQx;
    ref<Constraint> resLEQy;
    if (signednessInfo) {
        resLEQx = m_unsignedEncoding ? Atom::create(res, x, Atom::Ule) : Atom::create(res, x, Atom::Sle);
        resLEQy = m_unsignedEncoding ? Atom::create(res, y, Atom::Ule) : Atom::create(res, y, Atom::Sle);
    }
    else {
        resLEQx = Atom::create(res, x, Atom::Leq);
        resLEQy = Atom::create(res, y, Atom::Leq);
    }
    //</Negar>
    if (m_unsignedEncoding)
    {
        return Operator::create(resLEQx, resLEQy, Operator::And);
    }
    ref<Polynomial> null = Polynomial::null;
    //<Negar>
    ref<Constraint> xGEQnull;
    ref<Constraint> yGEQnull;
    ref<Constraint> resGEQnull;
    ref<Constraint> xLSSnull;
    ref<Constraint> yLSSnull;
    ref<Constraint> resLSSnull;
    if (signednessInfo) {
        xGEQnull = Atom::create(x, null, Atom::Sge);
        yGEQnull = Atom::create(y, null, Atom::Sge);
        resGEQnull = Atom::create(res, null, Atom::Sge);
        xLSSnull = Atom::create(x, null, Atom::Slt);
        yLSSnull = Atom::create(y, null, Atom::Slt);
        resLSSnull = Atom::create(res, null, Atom::Slt);
    }
    else {
        xGEQnull = Atom::create(x, null, Atom::Geq);
        yGEQnull = Atom::create(y, null, Atom::Geq);
        resGEQnull = Atom::create(res, null, Atom::Geq);
        xLSSnull = Atom::create(x, null, Atom::Lss);
        yLSSnull = Atom::create(y, null, Atom::Lss);
        resLSSnull = Atom::create(res, null, Atom::Lss);
    }
    //</Negar>
    // case 1: x >= 0 /\ y >= 0 /\ res >= 0 /\ res <= x /\ res <= y
    ref<Constraint> case1 = Operator::create(xGEQnull, yGEQnull, Operator::And);
    case1 = Operator::create(case1, resGEQnull, Operator::And);
    case1 = Operator::create(case1, resLEQx, Operator::And);
    case1 = Operator::create(case1, resLEQy, Operator::And);
    // case 2: x >= 0 /\ y < 0 /\ res >= 0 /\ res <= x
    ref<Constraint> case2 = Operator::create(xGEQnull, yLSSnull, Operator::And);
    case2 = Operator::create(case2, resGEQnull, Operator::And);
    case2 = Operator::create(case2, resLEQx, Operator::And);
    // case 3: x < 0 /\ y >= 0 /\ res >= 0 /\ res <= y
    ref<Constraint> case3 = Operator::create(xLSSnull, yGEQnull, Operator::And);
    case3 = Operator::create(case3, resGEQnull, Operator::And);
    case3 = Operator::create(case3, resLEQy, Operator::And);
    // case 4: x < 0 /\ y < 0 /\ res < 0 /\ res <= x /\ res <= y
    ref<Constraint> case4 = Operator::create(xLSSnull, yLSSnull, Operator::And);
    case4 = Operator::create(case4, resLSSnull, Operator::And);
    case4 = Operator::create(case4, resLEQx, Operator::And);
    case4 = Operator::create(case4, resLEQy, Operator::And);
    // disjunct...
    ref<Constraint> disj = Operator::create(case1, case2, Operator::Or);
    disj = Operator::create(disj, case3, Operator::Or);
    disj = Operator::create(disj, case4, Operator::Or);

    return disj;
}

void Converter::visitAnd(llvm::BinaryOperator &I)
{
    if (I.getType() == m_boolType)
    {
        return;
    }
    if (m_phase1)
    {
        m_vars.push_back(getVar(&I));
    }
    else
    {
        if (m_boundedIntegers && m_bitwiseConditions)
        {
            ref<Polynomial> x = getPolynomial(I.getOperand(0));
            ref<Polynomial> y = getPolynomial(I.getOperand(1));
            ref<Polynomial> nondef = Polynomial::create(getNondef(&I));
            ref<Constraint> c = getAndConstraintForBounded(x, y, nondef);
            visitGenericInstruction(I, nondef, c);
        }
        else
        {
            ref<Polynomial> nondef = Polynomial::create(getNondef(&I));
            visitGenericInstruction(I, nondef);

            //<Negar>
            std::string varName = I.getName().str();
            llvm::Value *firstOperand = I.getOperand(0);
            std::string firstOperandStr;
            if (auto *constInt = llvm::dyn_cast<llvm::ConstantInt>(firstOperand)) {
                firstOperandStr = std::to_string(constInt->getSExtValue());
            }
            else {
                firstOperandStr = "v" + firstOperand->getName().str();
            }
            llvm::Value *secondOperand = I.getOperand(1);
            std::string secondOperandStr;
            if (auto *constInt = llvm::dyn_cast<llvm::ConstantInt>(secondOperand)) {
                secondOperandStr = std::to_string(constInt->getSExtValue());
            }
            else {
                secondOperandStr = "v" + secondOperand->getName().str();
            }
            std::cout << "v" << varName << " := and(" << firstOperandStr << ", " << secondOperandStr << ");" << std::endl;
            //</Negar>
        }
    }
}

ref<Constraint> Converter::getOrConstraintForBounded(ref<Polynomial> x, ref<Polynomial> y, ref<Polynomial> res)
{
    //<Negar>
    ref<Constraint> resGEQx;
    ref<Constraint> resGEQy;
    if (signednessInfo) {
        resGEQx = m_unsignedEncoding ? Atom::create(res, x, Atom::Ule) : Atom::create(res, x, Atom::Sle);
        resGEQy = m_unsignedEncoding ? Atom::create(res, y, Atom::Ule) : Atom::create(res, y, Atom::Sle);
    }
    else {
        resGEQx = Atom::create(res, x, Atom::Leq);
        resGEQy = Atom::create(res, y, Atom::Leq);
    }
    //</Negar>
    if (m_unsignedEncoding)
    {
        return Operator::create(resGEQx, resGEQy, Operator::And);
    }
    ref<Polynomial> null = Polynomial::null;
    //<Negar>
    ref<Constraint> xGEQnull;
    ref<Constraint> yGEQnull;
    ref<Constraint> resGEQnull;
    ref<Constraint> xLSSnull;
    ref<Constraint> yLSSnull;
    ref<Constraint> resLSSnull;
    if (signednessInfo) {
        xGEQnull = Atom::create(x, null, Atom::Sge);
        yGEQnull = Atom::create(y, null, Atom::Sge);
        resGEQnull = Atom::create(res, null, Atom::Sge);
        xLSSnull = Atom::create(x, null, Atom::Slt);
        yLSSnull = Atom::create(y, null, Atom::Slt);
        resLSSnull = Atom::create(res, null, Atom::Slt);
    }
    else {
        xGEQnull = Atom::create(x, null, Atom::Geq);
        yGEQnull = Atom::create(y, null, Atom::Geq);
        resGEQnull = Atom::create(res, null, Atom::Geq);
        xLSSnull = Atom::create(x, null, Atom::Lss);
        yLSSnull = Atom::create(y, null, Atom::Lss);
        resLSSnull = Atom::create(res, null, Atom::Lss);
    }
    //</Negar>
    // case 1: x >= 0 /\ y >= 0 /\ res >= 0 /\ res >= x /\ res >= y
    ref<Constraint> case1 = Operator::create(xGEQnull, yGEQnull, Operator::And);
    case1 = Operator::create(case1, resGEQnull, Operator::And);
    case1 = Operator::create(case1, resGEQx, Operator::And);
    case1 = Operator::create(case1, resGEQy, Operator::And);
    // case 2: x >= 0 /\ y < 0 /\ res < 0 /\ res >= y
    ref<Constraint> case2 = Operator::create(xGEQnull, yLSSnull, Operator::And);
    case2 = Operator::create(case2, resLSSnull, Operator::And);
    case2 = Operator::create(case2, resGEQy, Operator::And);
    // case 3: x < 0 /\ y >= 0 /\ res < 0 /\ res >= x
    ref<Constraint> case3 = Operator::create(xLSSnull, yGEQnull, Operator::And);
    case3 = Operator::create(case3, resLSSnull, Operator::And);
    case3 = Operator::create(case3, resGEQx, Operator::And);
    // case 4: x < 0 /\ y < 0 /\ res < 0 /\ res >= x /\ res >= y
    ref<Constraint> case4 = Operator::create(xLSSnull, yLSSnull, Operator::And);
    case4 = Operator::create(case4, resLSSnull, Operator::And);
    case4 = Operator::create(case4, resGEQx, Operator::And);
    case4 = Operator::create(case4, resGEQy, Operator::And);
    // disjunct...
    ref<Constraint> disj = Operator::create(case1, case2, Operator::Or);
    disj = Operator::create(disj, case3, Operator::Or);
    disj = Operator::create(disj, case4, Operator::Or);

    return disj;
}

void Converter::visitOr(llvm::BinaryOperator &I)
{
    if (I.getType() == m_boolType)
    {
        return;
    }
    if (m_phase1)
    {
        m_vars.push_back(getVar(&I));
    }
    else
    {
        if (m_boundedIntegers && m_bitwiseConditions)
        {
            ref<Polynomial> x = getPolynomial(I.getOperand(0));
            ref<Polynomial> y = getPolynomial(I.getOperand(1));
            ref<Polynomial> nondef = Polynomial::create(getNondef(&I));
            ref<Constraint> c = getOrConstraintForBounded(x, y, nondef);
            visitGenericInstruction(I, nondef, c);
        }
        else
        {
            ref<Polynomial> nondef = Polynomial::create(getNondef(&I));
            visitGenericInstruction(I, nondef);

            //<Negar>
            std::string varName = I.getName().str();
            llvm::Value *firstOperand = I.getOperand(0);
            std::string firstOperandStr;
            if (auto *constInt = llvm::dyn_cast<llvm::ConstantInt>(firstOperand)) {
                firstOperandStr = std::to_string(constInt->getSExtValue());
            }
            else {
                firstOperandStr = "v" + firstOperand->getName().str();
            }
            llvm::Value *secondOperand = I.getOperand(1);
            std::string secondOperandStr;
            if (auto *constInt = llvm::dyn_cast<llvm::ConstantInt>(secondOperand)) {
                secondOperandStr = std::to_string(constInt->getSExtValue());
            }
            else {
                secondOperandStr = "v" + secondOperand->getName().str();
            }
            std::cout << "v" << varName << " := or(" << firstOperandStr << ", " << secondOperandStr << ");" << std::endl;
            //</Negar>
        }
    }
}

void Converter::visitXor(llvm::BinaryOperator &I)
{
    if (I.getType() == m_boolType)
    {
        return;
    }
    if (m_phase1)
    {
        m_vars.push_back(getVar(&I));
    }
    else
    {
        if (llvm::isa<llvm::ConstantInt>(I.getOperand(1)) && llvm::cast<llvm::ConstantInt>(I.getOperand(1))->isAllOnesValue())
        {
            // it is xor %i, -1 --> actually, it is -%i - 1
            ref<Polynomial> p1 = getPolynomial(I.getOperand(0));
            ref<Polynomial> p2 = Polynomial::one;
            visitGenericInstruction(I, p1->constMult(Polynomial::_negone)->sub(p2));
        }
        else
        {
            ref<Polynomial> nondef = Polynomial::create(getNondef(&I));
            visitGenericInstruction(I, nondef);
        }
    }
}

void Converter::visitCallInst(llvm::CallInst &I)
{
    llvm::CallSite callSite(&I);
    llvm::Function *calledFunction = callSite.getCalledFunction();
    if (calledFunction != NULL)
    {
        llvm::StringRef functionName = calledFunction->getName();
    }

    if (m_phase1)
    {
        if (I.getType() != m_boolType && I.getType()->isIntegerTy())
        {
            m_vars.push_back(getVar(&I));
        }
    }
    else
    {
        //<Negar>
        if (llvm::Function *CF = I.getCalledFunction()) {
            if (CF->isIntrinsic()) {
                if (CF->getIntrinsicID() == llvm::Intrinsic::memcpy) {
                    std::string leftVar = I.getOperand(0)->getName().str();
                    std::string rightVar = I.getOperand(1)->getName().str();
                    std::cout << "v" << leftVar << " := v" << rightVar << ";" << std::endl;
                }
            }
        }
        //</Negar>

        llvm::CallSite callSite(&I);
        llvm::Function *calledFunction = callSite.getCalledFunction();
        if (calledFunction != NULL)
        {
            llvm::StringRef functionName = calledFunction->getName();
            if (functionName == "__kittel_assume")
            {
                if (m_assumeIsControl)
                {
                    m_controlPoints.insert(getEval(m_counter));
                }
                ref<Constraint> c = m_onlyLoopConditions ? Constraint::_true : getConditionFromValue(callSite.getArgument(0));
                visitGenericInstruction(I, m_lhs, c->toNNF(false));
                return;
            }
            else if (functionName.startswith("__kittel_nondef"))
            {
                ref<Polynomial> nondef = Polynomial::create(getNondef(&I));
                visitGenericInstruction(I, nondef);
                return;
            }
        }
        if (m_complexityTuples)
        {
            m_controlPoints.insert(getEval(m_counter));
            m_controlPoints.insert(getEval(m_counter + 1));
            m_complexityLHSs.insert(getEval(m_counter));
        }
        // "random" functions
        if (I.getType()->isIntegerTy() || I.getType()->isVoidTy() || I.getType()->isFloatingPointTy() || I.getType()->isPointerTy() || I.getType()->isVectorTy() || I.getType()->isStructTy() || I.getType()->isArrayTy())
        {
            std::list<llvm::Function *> callees;
            if (calledFunction != NULL)
            {
                callees.push_back(calledFunction);
            }
            else
            {
                callees = getMatchingFunctions(I);
            }
            std::set<llvm::GlobalVariable *> toZap;
            m_idMap.insert(std::make_pair(&I, m_counter));
            ref<Term> lhs = Term::create(getEval(m_counter), m_lhs);
            for (std::list<llvm::Function *>::iterator cf = callees.begin(), cfe = callees.end(); cf != cfe; ++cf)
            {
                llvm::Function *callee = *cf;
                if (m_scc.find(callee) != m_scc.end() || m_complexityTuples)
                {
                    std::list<ref<Polynomial>> callArgs;
                    for (llvm::CallSite::arg_iterator i = callSite.arg_begin(), e = callSite.arg_end(); i != e; ++i)
                    {
                        llvm::Value *arg = *i;
                        if (arg->getType() != m_boolType && arg->getType()->isIntegerTy())
                        {
                            callArgs.push_back(getPolynomial(arg));
                        }
                    }
                    for (std::list<llvm::GlobalVariable *>::iterator i = m_globals.begin(), e = m_globals.end(); i != e; ++i)
                    {
                        callArgs.push_back(getPolynomial(*i));
                    }
                    m_controlPoints.insert(getEval(callee, "start"));
                    ref<Term> rhs2 = Term::create(getEval(callee, "start"), callArgs);
                    ref<Rule> rule2 = Rule::create(lhs, rhs2, Constraint::_true);
                    m_blockRules.push_back(rule2);
                }
                if (callee->isDeclaration())
                {
                    // they don't mess with globals
                    continue;
                }
                std::map<llvm::Function *, std::set<llvm::GlobalVariable *>>::iterator it = m_funcMayZap.find(callee);
                if (it == m_funcMayZap.end())
                {
                    std::cerr << "Could not find alias information (" << __FILE__ << ":" << __LINE__ << ")!" << std::endl;
                    exit(767);
                }
                std::set<llvm::GlobalVariable *> zapped = it->second;
                toZap.insert(zapped.begin(), zapped.end());
            }
            m_counter++;
            // zap!
            std::list<ref<Polynomial>> newArgs;
            if (I.getType()->isIntegerTy() && I.getType() != m_boolType)
            {
                ref<Polynomial> nondef = Polynomial::create(getNondef(&I));

                if (m_t2Output)
                {
                    //<Negar>
                    if (nondetTypeInfo) {
                        llvm::Function *calledFunc = I.getCalledFunction();
                        if (calledFunc) {
                            std::string funcName = calledFunc->getName().str();
                            const std::string prefix = "__VERIFIER_nondet_";
                            if (funcName.find(prefix) == 0) {
                                std::string typeSuffix = funcName.substr(prefix.size());
                                std::cout << (getVar(&I)) << " := nondet_" + typeSuffix + "();" << std::endl;
                            }
                        }
                    }
                    else {
                    //</Negar>

                        //std::cout << (nondef->toString()) << ":= nondet();" << std::endl;
                        std::cout << (getVar(&I)) << " := nondet();" << std::endl;

                    //<Negar>
                    }
                    //</Negar>
                }

                newArgs = getZappedArgs(toZap, I, nondef);
            }
            else
            {
                newArgs = getZappedArgs(toZap);
            }
            ref<Term> rhs1 = Term::create(getEval(m_counter), newArgs);
            ref<Rule> rule1 = Rule::create(lhs, rhs1, Constraint::_true);
            m_blockRules.push_back(rule1);
            return;
        }
        else
        {
            std::cerr << "Unsupported function return type encountered!" << std::endl;
            exit(1);
        }
    }
}

std::list<llvm::Function *> Converter::getMatchingFunctions(llvm::CallInst &I)
{
    std::list<llvm::Function *> res;
    const llvm::Type *type = I.getCalledValue()->getType();
    llvm::Module *module = I.getParent()->getParent()->getParent();
    for (llvm::Module::iterator i = module->begin(), e = module->end(); i != e; ++i)
    {
        if (!i->isDeclaration())
        {
            if (i->getType() == type)
            {
                res.push_back(i);
            }
        }
    }
    return res;
}

std::string Converter::getNondef(llvm::Value *V)
{
    std::ostringstream tmp;
    tmp << "nondef." << m_nondef;
    m_nondef++;
    std::string res = tmp.str();
    if (m_boundedIntegers && V != NULL && V->getType()->isIntegerTy())
    {
        m_bitwidthMap.insert(std::make_pair(res, llvm::cast<llvm::IntegerType>(V->getType())->getBitWidth()));
    }
    return res;
}

void Converter::visitSelectInst(llvm::SelectInst &I)
{
    if (I.getType() == m_boolType || !I.getType()->isIntegerTy())
    {
        return;
    }
    if (m_phase1)
    {
        m_vars.push_back(getVar(&I));
    }
    else
    {
        if (m_selectIsControl)
        {
            m_controlPoints.insert(getEval(m_counter));
        }
        llvm::BasicBlock *pBlock = I.getParent();
        m_idMap.insert(std::make_pair(&I, m_counter));
        ref<Term> lhs = Term::create(getEval(m_counter), m_lhs);
        m_counter++;
        ref<Term> rhs1 = Term::create(getEval(m_counter), getNewArgs(I, getPolynomial(I.getTrueValue())));
        ref<Term> rhs2 = Term::create(getEval(m_counter), getNewArgs(I, getPolynomial(I.getFalseValue())));
        ref<Constraint> c = m_onlyLoopConditions ? Constraint::_true : getConditionFromValue(I.getCondition());
        ref<Rule> rule1 = Rule::create(lhs, rhs1, c->toNNF(false));
        m_blockRules.push_back(rule1);
        ref<Rule> rule2 = Rule::create(lhs, rhs2, c->toNNF(true));
        m_blockRules.push_back(rule2);

        if (m_t2Output)
        {
            //Given then we're branching, create an intermediate node to branch through via condition.
            std::cout << "TO: " << (pBlock->getName().str()) << "_" << (getVar(&I)) << ";" << std::endl;

            //Branch to assignment where condition is true.
            std::cout << "FROM: " << (pBlock->getName().str()) << "_" << (getVar(&I)) << ";" << std::endl;
            std::cout << "assume(" << (c->toT2String()) << ");" << std::endl;
            std::cout << (getVar(&I)) << " := " << (getPolynomial(I.getTrueValue()))->toString() << ";" << std::endl;
            std::cout << "TO: " << (pBlock->getName().str()) << "_s" << (getVar(&I)) << ";" << std::endl
                      << std::endl;

            //Branch to assignment where condition is false.
            std::cout << "FROM: " << (pBlock->getName().str()) << "_" << (getVar(&I)) << ";" << std::endl;
            std::cout << "assume(" << ((c->toNNF(true))->toT2String()) << ");" << std::endl;
            std::cout << (getVar(&I)) << " := " << (getPolynomial(I.getFalseValue()))->toString() << ";" << std::endl;
            std::cout << "TO: " << (pBlock->getName().str()) << "_s" << (getVar(&I)) << ";" << std::endl
                      << std::endl;

            //Create final intermediate transition to merge back the above branching.
            std::cout << "FROM: " << (pBlock->getName().str()) << "_s" << (getVar(&I)) << ";" << std::endl;
        }
    }
}

void Converter::visitPHINode(llvm::PHINode &I)
{
    if (I.getType() == m_boolType || !I.getType()->isIntegerTy())
    {
        //<Negar>
        //if (!m_phase1) {
        //    std::string phiVarName = I.getName().str();
        //    std::cout << "v" << phiVarName << " := " << "var__temp_v" + phiVarName << ";" << std::endl;
        //}
        //</Negar>

        return;
    }
    std::string phiVar = getVar(&I);
    if (m_phase1)
    {
        m_vars.push_back(phiVar);
        m_phiVars.insert(phiVar);
        std::string valName;
        unsigned incomeVals = I.getNumIncomingValues();
        for (unsigned i = 0; i < incomeVals; i++)
        {
            llvm::BasicBlock *iBlock = I.getIncomingBlock(i);
            llvm::Value *iValue = I.getIncomingValueForBlock(iBlock);
            std::map<llvm::BasicBlock *, std::list<std::pair<std::string, llvm::Value *>>>::iterator it = m_phiMap.find(iBlock);
            if (it != m_phiMap.end())
            {
                it->second.push_back(std::make_pair(phiVar, iValue));
            }
            else
            {
                std::list<std::pair<std::string, llvm::Value *>> valList;
                valList.push_back(std::make_pair(phiVar, iValue));
                m_phiMap[iBlock] = valList;
            }
        }
    }
    else
    {
        std::string varAssign = "var__temp_" + phiVar;
        std::string varOrig = phiVar;
        if (m_t2Output)
        {
            std::cout << varOrig << " := " << varAssign << ";" << std::endl;
        }
    }
}

//<Negar>
void Converter::visitGetElementPtrInst(llvm::GetElementPtrInst &gepInst)
{
    if (!m_phase1) {
        llvm::Type *ptrType = gepInst.getPointerOperandType()->getPointerElementType();
        if (ptrType->isArrayTy()) {
            // Access an element of an array -> One-dimensional -> Fixed-index OR Variable-index
            std::string arrayName = gepInst.getPointerOperand()->getName().str();
            if (arrayName.find(".str") == std::string::npos && arrayName.find("__PRETTY_FUNCTION__.") == std::string::npos) {
                std::string varName = gepInst.getName().str();
                llvm::Value *arrayIndexOperand = gepInst.getOperand(gepInst.getNumOperands() - 1);
                std::string index;
                if (auto *constInt = llvm::dyn_cast<llvm::ConstantInt>(arrayIndexOperand)) {
                    // Fixed-index
                    index = std::to_string(constInt->getSExtValue());
                }
                else {
                    // Variable-index
                    index = "v" + arrayIndexOperand->getName().str();
                }
                llvm::Type *elementType = llvm::dyn_cast<llvm::ArrayType>(ptrType)->getElementType();
                if (elementType->isIntegerTy(8) || elementType->isIntegerTy(32) || elementType->isIntegerTy(64)) { // char, int, or long
                    std::cout << "v" << varName << " := " << index << ";" << std::endl;
                }
                else if (elementType->isStructTy()) { // struct
                    std::cout << "v" << varName << " := select_array(v" << arrayName << ", " << index << ");" << std::endl;
                }
                getElementPtrInsts.push_back({"v" + varName, "v" + arrayName, index});
                arrayInsts.push_back({"v" + varName, "v" + arrayName, index});
            }
        }
        else if (ptrType->isStructTy()) {
            if (gepInst.getNumOperands() == 3) {
                // Access a field of a structure
                std::string varName = gepInst.getName().str();
                std::string structInstance = gepInst.getPointerOperand()->getName().str();
                llvm::Value *accessedField = gepInst.getOperand(gepInst.getNumOperands() - 1);
                int accessedFieldId = llvm::dyn_cast<llvm::ConstantInt>(accessedField)->getSExtValue();
                int totalFields = llvm::cast<llvm::StructType>(ptrType)->getNumElements();
                structInsts.push_back({"v" + varName, "v" + structInstance, accessedFieldId, totalFields});
            }
            else {
                //<second>
                std::string basePoint = gepInst.getPointerOperand()->getName().str();
                if (std::find(oneDimArrs.begin(), oneDimArrs.end(), "v" + basePoint) != oneDimArrs.end()) {
                    // Access an element of an array -> One-dimensional -> Flexible access -> 1 (struct)
                    std::string varName = gepInst.getName().str();
                    llvm::Value *arrayIndexOperand = gepInst.getOperand(gepInst.getNumOperands() - 1);
                    std::string index;
                    if (auto *constInt = llvm::dyn_cast<llvm::ConstantInt>(arrayIndexOperand)) {
                        index = std::to_string(constInt->getSExtValue());
                    }
                    else {
                        index = "v" + arrayIndexOperand->getName().str();
                    }
                    std::cout << "v" << varName << " := select_array(v" << basePoint << ", " << index << ");" << std::endl;
                    arrayInsts.push_back({"v" + varName, "v" + basePoint, index});
                }
                else {
                    // Access an element of an array -> One-dimensional -> Flexible access -> 2 (struct)
                    std::string varName = gepInst.getName().str();
                    auto it = std::find_if(getElementPtrInsts.begin(), getElementPtrInsts.end(), [&basePoint](const GetElementPtrInst& getElementPtrInst) { return getElementPtrInst.variable == "v" + basePoint; });
                    std::string arrayName = it->array;
                    std::string index = it->index;
                    llvm::Value *offsetOperand = gepInst.getOperand(gepInst.getNumOperands() - 1);
                    std::string offset;
                    if (auto *constInt = llvm::dyn_cast<llvm::ConstantInt>(offsetOperand)) {
                        offset = std::to_string(constInt->getSExtValue());
                    }
                    else {
                        offset = "v" + offsetOperand->getName().str();
                    }
                    std::cout << "v" << varName << " := select_array(" << arrayName << ", " << index << " + " << offset << ");" << std::endl;
                    arrayInsts.push_back({"v" + varName, arrayName, index + " + " + offset});
                }
                //</second>
            }
        }
        else {
            //<first>
            std::string basePoint = gepInst.getPointerOperand()->getName().str();
            if (std::find(oneDimArrs.begin(), oneDimArrs.end(), "v" + basePoint) != oneDimArrs.end()) {
                // Access an element of an array -> One-dimensional -> Flexible access -> 1 (anything except struct)
                std::string varName = gepInst.getName().str();
                llvm::Value *arrayIndexOperand = gepInst.getOperand(gepInst.getNumOperands() - 1);
                std::string index;
                if (auto *constInt = llvm::dyn_cast<llvm::ConstantInt>(arrayIndexOperand)) {
                    index = std::to_string(constInt->getSExtValue());
                }
                else {
                    index = "v" + arrayIndexOperand->getName().str();
                }
                std::cout << "v" << varName << " := " << index << ";" << std::endl;
                arrayInsts.push_back({"v" + varName, "v" + basePoint, index});
            }
            else if (std::find(twoDimOuterArrs.begin(), twoDimOuterArrs.end(), "v" + basePoint) != twoDimOuterArrs.end()) {
                // Access an element of an array -> Two-dimensional -> Row
                std::string varName = gepInst.getName().str();
                llvm::Value *arrayIndexOperand = gepInst.getOperand(gepInst.getNumOperands() - 1);
                std::string index;
                if (auto *constInt = llvm::dyn_cast<llvm::ConstantInt>(arrayIndexOperand)) {
                    index = std::to_string(constInt->getSExtValue());
                }
                else {
                    index = "v" + arrayIndexOperand->getName().str();
                }
                std::cout << "v" << varName << " := select_array(v" << basePoint << ", " << index << ");" << std::endl;
                if (std::find(twoDimInnerArrs.begin(), twoDimInnerArrs.end(), "v" + varName) == twoDimInnerArrs.end()) {
                    twoDimInnerArrs.push_back("v" + varName);
                }
                arrayInsts.push_back({"v" + varName, "v" + basePoint, index});
            }
            else if (std::find(twoDimInnerArrs.begin(), twoDimInnerArrs.end(), "v" + basePoint) != twoDimInnerArrs.end()) {
                // Access an element of an array -> Two-dimensional -> Column
                std::string varName = gepInst.getName().str();
                llvm::Value *arrayIndexOperand = gepInst.getOperand(gepInst.getNumOperands() - 1);
                std::string index;
                if (auto *constInt = llvm::dyn_cast<llvm::ConstantInt>(arrayIndexOperand)) {
                    index = std::to_string(constInt->getSExtValue());
                }
                else {
                    index = "v" + arrayIndexOperand->getName().str();
                }
                std::cout << "v" << varName << " := " << index << ";" << std::endl;
                arrayInsts.push_back({"v" + varName, "v" + basePoint, index});
            }
            else {
                // Access an element of an array -> One-dimensional -> Flexible access -> 2 (anything except struct)
                std::string varName = gepInst.getName().str();
                auto it = std::find_if(getElementPtrInsts.begin(), getElementPtrInsts.end(), [&basePoint](const GetElementPtrInst& getElementPtrInst) { return getElementPtrInst.variable == "v" + basePoint; });
                std::string arrayName = it->array;
                std::string index = it->index;
                llvm::Value *offsetOperand = gepInst.getOperand(gepInst.getNumOperands() - 1);
                std::string offset;
                if (auto *constInt = llvm::dyn_cast<llvm::ConstantInt>(offsetOperand)) {
                    offset = std::to_string(constInt->getSExtValue());
                }
                else {
                    offset = "v" + offsetOperand->getName().str();
                }
                std::cout << "v" << varName << " := " << index << " + " << offset << ";" << std::endl;
                arrayInsts.push_back({"v" + varName, arrayName, index + " + " + offset});
            }
            //</first>
        }
    }
}
//</Negar>

void Converter::visitIntToPtrInst(llvm::IntToPtrInst &)
{
}

void Converter::visitBitCastInst(llvm::BitCastInst &I)
{
    if (!I.getType()->isIntegerTy())
    {
        //<Negar>
        //if(!m_phase1){
        //    std::string leftVar = I.getName().str();
        //    std::string rightVar = I.getOperand(0)->getName().str();
        //    std::cout << "v" << leftVar << " := select_array(v" << rightVar << ", 0);" << std::endl;
        //    arrayInsts.push_back({"v" + leftVar, "v" + rightVar, "0"});
        //}
        //</Negar>

        return;
    }
    if (m_phase1)
    {
        m_vars.push_back(getVar(&I));
    }
    else
    {
        ref<Polynomial> value = getPolynomial(&I);
        visitGenericInstruction(I, value);
    }
}

void Converter::visitPtrToIntInst(llvm::PtrToIntInst &I)
{
    if (m_phase1)
    {
        m_vars.push_back(getVar(&I));
    }
    else
    {
        ref<Polynomial> nondef = Polynomial::create(getNondef(&I));
        visitGenericInstruction(I, nondef);
    }
}

void Converter::visitLoadInst(llvm::LoadInst &I)
{
    if (!I.getType()->isIntegerTy() || I.getType() == m_boolType)
    {
        return;
    }
    if (m_phase1)
    {
        m_vars.push_back(getVar(&I));
    }
    else
    {
        MayMustMap::iterator it = m_mmMap.find(&I);
        if (it == m_mmMap.end())
        {
            std::cerr << "Could not find alias information (" << __FILE__ << ":" << __LINE__ << ")!" << std::endl;
            exit(321);
        }
        MayMustPair mmp = it->second;
        std::set<llvm::GlobalVariable *> mays = mmp.first;
        std::set<llvm::GlobalVariable *> musts = mmp.second;
        ref<Polynomial> newArg;
        if (musts.size() == 1 && mays.size() == 0 &&
            (m_t2Output && I.isSimple()))
        {
            // unique!
            newArg = Polynomial::create(getVar(*musts.begin()));
        }
        else
        {
            // nondef...
            newArg = Polynomial::create(getNondef(&I));

            //<Negar>
            std::string sourceVar = "v" + I.getPointerOperand()->getName().str();
            std::string destinationVar = getVar(&I);

            auto it1 = std::find_if(arrayInsts.begin(), arrayInsts.end(), [&sourceVar](const ArrayInst& arrayInst) { return arrayInst.variable == sourceVar; });
            if (it1 != arrayInsts.end()) {
                newArg = Polynomial::create("nondef_nf");
                std::cout << destinationVar << " := " << "select_array(" << it1->array << ", " << sourceVar << ");" << std::endl;
            }

            else {
                auto it2 = std::find_if(structInsts.begin(), structInsts.end(), [&sourceVar](const StructInst& structInst) { return structInst.variable == sourceVar; });
                if (it2 != structInsts.end()) {
                    newArg = Polynomial::create("nondef_nf");
                    std::cout << destinationVar << " := select_tuple(" << it2->instance << ", " << std::to_string(it2->accessedFieldId) << ", " + std::to_string(it2->totalFields) + ");" << std::endl;
                }
            }
            //</Negar>
        }
        m_idMap.insert(std::make_pair(&I, m_counter));
        ref<Term> lhs = Term::create(getEval(m_counter), m_lhs);
        ++m_counter;
        ref<Term> rhs = Term::create(getEval(m_counter), getNewArgs(I, newArg));
        ref<Rule> rule = Rule::create(lhs, rhs, Constraint::_true);
        if (m_t2Output)
        {
            //<Negar>
            if (newArg->toString() != "nondef_nf") {
            //</Negar>

                //std::cout << (nondef->toString()) << ":= nondet();" << std::endl;
                //std::cout << (getVar(&I)) << " := nondet();" << std::endl;
                std::cout << (getVar(&I)) << " := "
                          << newArg->toString() << ";" << std::endl;

            //<Negar>
            }
            //</Negar>
        }
        m_blockRules.push_back(rule);
    }
}

void Converter::visitStoreInst(llvm::StoreInst &I)
{
    if (m_phase1)
    {
    }
    else if (m_t2Output && I.isSimple())
    {
        llvm::Value *val = I.getValueOperand();
        llvm::Value *ptr = I.getPointerOperand();
        ref<Polynomial> p = getPolynomial(val);

        //<Negar>
        bool flag = false;

        std::string sourceVar = p->toString();
        std::string destinationVar = getVar(ptr);

        auto it1 = std::find_if(arrayInsts.begin(), arrayInsts.end(), [&destinationVar](const ArrayInst& arrayInst) { return arrayInst.variable == destinationVar; });
        if (it1 != arrayInsts.end()) {
            flag = true;
            std::string arrayName = it1->array;

            if (std::find(oneDimArrs.begin(), oneDimArrs.end(), arrayName) != oneDimArrs.end()) {
                std::cout << arrayName << " := store_array(" << arrayName << ", " << destinationVar << ", " << sourceVar << ");" << std::endl;
            }

            else {
                std::cout << arrayName << " := store_array(" << arrayName << ", " << destinationVar << ", " << sourceVar << ");" << std::endl;
                auto it2 = std::find_if(arrayInsts.begin(), arrayInsts.end(), [&arrayName](const ArrayInst& arrayInst) { return arrayInst.variable == arrayName; });
                if (it2 != arrayInsts.end()) {
                    std::cout << it2->array << " := store_array(" << it2->array << ", " << it2->index << ", " << arrayName << ");" << std::endl;
                }
            }
        }

        else {
            auto it3 = std::find_if(structInsts.begin(), structInsts.end(), [&destinationVar](const StructInst& structInst) { return structInst.variable == destinationVar; });
            if (it3 != structInsts.end()) {
                flag = true;
                std::string structInstance = it3->instance;
                auto it4 = std::find_if(arrayInsts.begin(), arrayInsts.end(), [&structInstance](const ArrayInst& arrayInst) { return arrayInst.variable == structInstance; });
                if (it4 != arrayInsts.end()) {
                    std::string newInst = it3->variable + "v" + std::to_string(it3->totalFields) + " := constr_tuple(";
                    for (int i = 0; i < it3->totalFields; i++) {
                        if (i == it3->accessedFieldId) {
                            newInst = newInst + sourceVar + ", ";
                        }
                        else {
                            std::cout << it3->variable << "v" << std::to_string(i) << " := select_tuple(" << structInstance << ", " << std::to_string(i) << ", " << it3->totalFields << ");" << std::endl;
                            newInst = newInst + it3->variable + "v" + std::to_string(i) + ", ";
                        }
                    }
                    newInst.erase(newInst.size() - 2);
                    newInst = newInst + ");";
                    std::cout << newInst << std::endl;
                    std::cout << it4->array << " := store_array(" << it4->array << ", " << it4->index << ", " << it3->variable + "v" + std::to_string(it3->totalFields) << ");" << std::endl;
                }
            }
        }

        if (flag != true) {
        //</Negar>

            std::cout << (getVar(ptr)) << " := "
                      << p->toString() << ";" << std::endl;

        //<Negar>
        }
        //</Negar>
    }
    else
    {
        llvm::Value *val = I.getOperand(0);
        MayMustMap::iterator it = m_mmMap.find(&I);
        if (it == m_mmMap.end())
        {
            std::cerr << "Could not find alias information (" << __FILE__ << ":" << __LINE__ << ")!" << std::endl;
            exit(321);
        }
        MayMustPair mmp = it->second;
        std::set<llvm::GlobalVariable *> mays = mmp.first;
        std::set<llvm::GlobalVariable *> musts = mmp.second;
        std::list<ref<Polynomial>> newArgs;
        if (musts.size() == 1 && mays.size() == 0)
        {
            // unique!
            newArgs = getNewArgs(**musts.begin(), getPolynomial(val));
        }
        else if (musts.size() != 0)
        {
            std::cerr << "Strange number of must aliases!" << std::endl;
            exit(1212);
        }
        else
        {
            // zap all that may
            newArgs = getZappedArgs(mays);
        }
        m_idMap.insert(std::make_pair(&I, m_counter));
        ref<Term> lhs = Term::create(getEval(m_counter), m_lhs);
        ++m_counter;
        ref<Term> rhs = Term::create(getEval(m_counter), newArgs);
        ref<Rule> rule = Rule::create(lhs, rhs, Constraint::_true);
        if (m_t2Output)
        {
            //std::cout << (nondef->toString()) << ":= nondet();" << std::endl;
            std::cout << (getVar(&I)) << " := nondet();" << std::endl;
        }
        m_blockRules.push_back(rule);
    }
}

//<Negar>
void Converter::visitAllocaInst(llvm::AllocaInst &allocaInst)
{
    if (m_phase1) {
    }
    else {
        llvm::Type *allocatedType = allocaInst.getAllocatedType();
        if (allocatedType->isArrayTy()) {
            // Define an array -> Locally -> One-dimensional -> Fixed-sized
            std::string arrayName = "v" + allocaInst.getName().str();
            std::cout << arrayName << " := nondet();" << std::endl;
            if (std::find(oneDimArrs.begin(), oneDimArrs.end(), arrayName) == oneDimArrs.end()) {
                oneDimArrs.push_back(arrayName);
            }
        }
        else {
            std::string arraySizeOperand = allocaInst.getArraySize()->getName().str();
            if (std::find(mulInsts.begin(), mulInsts.end(), "v" + arraySizeOperand) == mulInsts.end()) {
                // Define an array -> Locally -> One-dimensional -> Variable-sized
                std::string arrayName = "v" + allocaInst.getName().str();
                std::cout << arrayName << " := nondet();" << std::endl;
                if (std::find(oneDimArrs.begin(), oneDimArrs.end(), arrayName) == oneDimArrs.end()) {
                    oneDimArrs.push_back(arrayName);
                }
            }
            else {
                // Define an array -> Locally -> Two-dimensional
                std::string arrayName = "v" + allocaInst.getName().str();
                std::cout << arrayName << " := nondet();" << std::endl;
                if (std::find(twoDimOuterArrs.begin(), twoDimOuterArrs.end(), arrayName) == twoDimOuterArrs.end()) {
                    twoDimOuterArrs.push_back(arrayName);
                }
            }
        }
    }
}
//</Negar>

void Converter::visitFPToSIInst(llvm::FPToSIInst &I)
{
    if (m_phase1)
    {
        m_vars.push_back(getVar(&I));
    }
    else
    {
        //<Negar>
        std::string leftVar = I.getName().str();
        std::string rightVar = I.getOperand(0)->getName().str();
        std::cout << "v" << leftVar << " := real2int(v" << rightVar << ");" << std::endl;
        //</Negar>

        ref<Polynomial> nondef = Polynomial::create(getNondef(&I));
        visitGenericInstruction(I, nondef);
    }
}

void Converter::visitFPToUIInst(llvm::FPToUIInst &I)
{
    if (m_phase1)
    {
        m_vars.push_back(getVar(&I));
    }
    else
    {
        //<Negar>
        std::string leftVar = I.getName().str();
        std::string rightVar = I.getOperand(0)->getName().str();
        std::cout << "v" << leftVar << " := real2int(v" << rightVar << ");" << std::endl;
        //</Negar>

        ref<Polynomial> nondef = Polynomial::create(getNondef(&I));
        visitGenericInstruction(I, nondef);
    }
}

void Converter::visitInstruction(llvm::Instruction &I)
{
    if (I.getType() == m_boolType || !I.getType()->isIntegerTy())
    {
        return;
    }
    if (m_phase1)
    {
        m_vars.push_back(getVar(&I));
    }
    else
    {
        ref<Polynomial> nondef = Polynomial::create(getNondef(&I));
        visitGenericInstruction(I, nondef);
    }
}

void Converter::visitSExtInst(llvm::SExtInst &I)
{
    if (m_phase1)
    {
        m_vars.push_back(getVar(&I));
    }
    else
    {
        //<Negar>
        std::string leftVar = I.getName().str();
        std::string rightExpr;
        llvm::Value *op = I.getOperand(0);
        if (auto *CI = dyn_cast<llvm::ConstantInt>(op)) {
            rightExpr = std::to_string(CI->getSExtValue());
        }
        else {
            rightExpr = "v" + op->getName().str();
        }
        if (signednessInfo) {
            unsigned sourceBits = I.getOperand(0)->getType()->getIntegerBitWidth();
            unsigned destinationBits = I.getType()->getIntegerBitWidth();
            std::cout << "v" << leftVar << " := sign_extend(" << sourceBits << ", " << destinationBits << ", " << rightExpr << ");" << std::endl;
        }
        else {
            std::cout << "v" << leftVar << " := " << rightExpr << ";" << std::endl;
        }
        //</Negar>

        m_idMap.insert(std::make_pair(&I, m_counter));
        ref<Term> lhs = Term::create(getEval(m_counter), m_lhs);
        ref<Polynomial> copy = getPolynomial(I.getOperand(0));
        ++m_counter;
        if (m_boundedIntegers && m_unsignedEncoding)
        {
            unsigned int bitwidthNew = llvm::cast<llvm::IntegerType>(I.getType())->getBitWidth();
            unsigned int bitwidthOld = llvm::cast<llvm::IntegerType>(I.getOperand(0)->getType())->getBitWidth();
            ref<Polynomial> sizeNew = Polynomial::power_of_two(bitwidthNew);
            ref<Polynomial> sizeOld = Polynomial::power_of_two(bitwidthOld);
            ref<Polynomial> sizeDiff = sizeNew->sub(sizeOld);
            ref<Polynomial> intmaxOld = Polynomial::simax(bitwidthOld);
            ref<Polynomial> converted = sizeDiff->add(copy);
            ref<Term> rhs1 = Term::create(getEval(m_counter), getNewArgs(I, copy));
            ref<Term> rhs2 = Term::create(getEval(m_counter), getNewArgs(I, converted));
            //<Negar>
            ref<Constraint> c1;
            ref<Constraint> c2;
            if (signednessInfo) {
                c1 = Atom::create(copy, intmaxOld, Atom::Ule);
                c2 = Atom::create(copy, intmaxOld, Atom::Ugt);
            }
            else {
                c1 = Atom::create(copy, intmaxOld, Atom::Leq);
                c2 = Atom::create(copy, intmaxOld, Atom::Gtr);
            }
            //</Negar>
            ref<Rule> rule1 = Rule::create(lhs, rhs1, c1);
            ref<Rule> rule2 = Rule::create(lhs, rhs2, c2);
            m_blockRules.push_back(rule1);
            m_blockRules.push_back(rule2);
        }
        else
        {
            // mathematical integers or bounded integers with signed encoding
            ref<Term> rhs = Term::create(getEval(m_counter), getNewArgs(I, copy));
            ref<Rule> rule = Rule::create(lhs, rhs, Constraint::_true);
            m_blockRules.push_back(rule);
        }
    }
}

void Converter::visitZExtInst(llvm::ZExtInst &I)
{
    if (isAssumeArg(I))
    {
        return;
    }
    if (m_phase1)
    {
        m_vars.push_back(getVar(&I));
    }
    else
    {
        //<Negar>
        llvm::BasicBlock *basicBlock = I.getParent();
        std::string basicBlockName = basicBlock->getName().str();
        llvm::Value *preInst = I.getOperand(0);
        llvm::ICmpInst *preCmpInst = dyn_cast<llvm::ICmpInst>(preInst);
        if (preCmpInst) {
            llvm::ICmpInst::Predicate op = preCmpInst->getPredicate();
            std::string trueOp;
            std::string falseOp;
            if (signednessInfo) {
                switch (op) {
                    case llvm::ICmpInst::ICMP_EQ:
                        trueOp = "==";
                        falseOp = "!=";
                        break;
                    case llvm::ICmpInst::ICMP_NE:
                        trueOp = "!=";
                        falseOp = "==";
                        break;
                    case llvm::ICmpInst::ICMP_SLT:
                        trueOp = "slt";
                        falseOp = "sge";
                        break;
                    case llvm::ICmpInst::ICMP_SLE:
                        trueOp = "sle";
                        falseOp = "sgt";
                        break;
                    case llvm::ICmpInst::ICMP_SGT:
                        trueOp = "sgt";
                        falseOp = "sle";
                        break;
                    case llvm::ICmpInst::ICMP_SGE:
                        trueOp = "sge";
                        falseOp = "slt";
                        break;
                    case llvm::ICmpInst::ICMP_ULT:
                        trueOp = "ult";
                        falseOp = "uge";
                        break;
                    case llvm::ICmpInst::ICMP_ULE:
                        trueOp = "ule";
                        falseOp = "ugt";
                        break;
                    case llvm::ICmpInst::ICMP_UGT:
                        trueOp = "ugt";
                        falseOp = "ule";
                        break;
                    case llvm::ICmpInst::ICMP_UGE:
                        trueOp = "uge";
                        falseOp = "ult";
                        break;
                    default:
                        trueOp = "?";
                        falseOp = "!?";
                }
            } else {
                switch (op) {
                    case llvm::ICmpInst::ICMP_EQ:
                        trueOp = "==";
                        falseOp = "!=";
                        break;
                    case llvm::ICmpInst::ICMP_NE:
                        trueOp = "!=";
                        falseOp = "==";
                        break;
                    case llvm::ICmpInst::ICMP_SLT:
                    case llvm::ICmpInst::ICMP_ULT:
                        trueOp = "<";
                        falseOp = ">=";
                        break;
                    case llvm::ICmpInst::ICMP_SLE:
                    case llvm::ICmpInst::ICMP_ULE:
                        trueOp = "<=";
                        falseOp = ">";
                        break;
                    case llvm::ICmpInst::ICMP_SGT:
                    case llvm::ICmpInst::ICMP_UGT:
                        trueOp = ">";
                        falseOp = "<=";
                        break;
                    case llvm::ICmpInst::ICMP_SGE:
                    case llvm::ICmpInst::ICMP_UGE:
                        trueOp = ">=";
                        falseOp = "<";
                        break;
                    default:
                        trueOp = "?";
                        falseOp = "!?";
                }
            }
            llvm::Value *leftOperand = preCmpInst->getOperand(0);
            llvm::Value *rightOperand = preCmpInst->getOperand(1);
            std::string leftOperandStr;
            if (llvm::ConstantInt * CI = llvm::dyn_cast<llvm::ConstantInt>(leftOperand)) {
                leftOperandStr = std::to_string(CI->getSExtValue());
            } else if (leftOperand->hasName()) {
                leftOperandStr = "v" + leftOperand->getName().str();
            } else {
                leftOperandStr = "v" + std::to_string(leftOperand->getValueID());
            }
            std::string rightOperandStr;
            if (llvm::ConstantInt * CI = llvm::dyn_cast<llvm::ConstantInt>(rightOperand)) {
                rightOperandStr = std::to_string(CI->getSExtValue());
            } else if (rightOperand->hasName()) {
                rightOperandStr = "v" + rightOperand->getName().str();
            } else {
                rightOperandStr = "v" + std::to_string(rightOperand->getValueID());
            }
            std::string result;
            if (preCmpInst->hasName()) {
                result = "v" + preCmpInst->getName().str();
            } else {
                result = "v" + std::to_string(preCmpInst->getValueID());
            }
            std::cout << "TO: " << basicBlockName << "_" << result << ";\n\n";
            std::cout << "FROM: " << basicBlockName << "_" << result << ";\n";
            std::cout << "assume(" << leftOperandStr << " " << trueOp << " " << rightOperandStr << ");\n";
            std::cout << result << " := 1;\n";
            std::cout << "TO: " << basicBlockName << "_s" << result << ";\n\n";
            std::cout << "FROM: " << basicBlockName << "_" << result << ";\n";
            std::cout << "assume(" << leftOperandStr << " " << falseOp << " " << rightOperandStr << ");\n";
            std::cout << result << " := 0;\n";
            std::cout << "TO: " << basicBlockName << "_s" << result << ";\n\n";
            std::cout << "FROM: " << basicBlockName << "_s" << result << ";\n";
        }
        std::string leftVar = I.getName().str();
        std::string rightExpr;
        llvm::Value *op = I.getOperand(0);
        if (auto *CI = dyn_cast<llvm::ConstantInt>(op)) {
            rightExpr = std::to_string(CI->getSExtValue());
        }
        else {
            rightExpr = "v" + op->getName().str();
        }
        if (signednessInfo) {
            unsigned sourceBits = I.getOperand(0)->getType()->getIntegerBitWidth();
            unsigned destinationBits = I.getType()->getIntegerBitWidth();
            std::cout << "v" << leftVar << " := zero_extend(" << sourceBits << ", " << destinationBits << ", " << rightExpr << ");" << std::endl;
        }
        else {
            std::cout << "v" << leftVar << " := " << rightExpr << ";" << std::endl;
        }
        //</Negar>

        m_idMap.insert(std::make_pair(&I, m_counter));
        ref<Term> lhs = Term::create(getEval(m_counter), m_lhs);
        ++m_counter;
        if (I.getOperand(0)->getType() == m_boolType)
        {
            ref<Polynomial> zero = Polynomial::null;
            ref<Polynomial> one = Polynomial::one;
            ref<Term> rhszero = Term::create(getEval(m_counter), getNewArgs(I, zero));
            ref<Term> rhsone = Term::create(getEval(m_counter), getNewArgs(I, one));
            ref<Constraint> c = getConditionFromValue(I.getOperand(0));
            ref<Rule> rulezero = Rule::create(lhs, rhszero, c->toNNF(true));
            ref<Rule> ruleone = Rule::create(lhs, rhsone, c->toNNF(false));
            m_blockRules.push_back(rulezero);
            m_blockRules.push_back(ruleone);
        }
        else
        {
            ref<Polynomial> copy = getPolynomial(I.getOperand(0));
            if (m_boundedIntegers && !m_unsignedEncoding)
            {
                unsigned int bitwidthOld = llvm::cast<llvm::IntegerType>(I.getOperand(0)->getType())->getBitWidth();
                ref<Polynomial> shifter = Polynomial::power_of_two(bitwidthOld);
                ref<Polynomial> converted = shifter->add(copy);
                ref<Term> rhs1 = Term::create(getEval(m_counter), getNewArgs(I, copy));
                ref<Term> rhs2 = Term::create(getEval(m_counter), getNewArgs(I, converted));
                ref<Polynomial> zero = Polynomial::null;
                //<Negar>
                ref<Constraint> c1;
                ref<Constraint> c2;
                if (signednessInfo) {
                    ref<Constraint> c1 = Atom::create(copy, zero, Atom::Sge);
                    ref<Constraint> c2 = Atom::create(copy, zero, Atom::Slt);
                }
                else {
                    ref<Constraint> c1 = Atom::create(copy, zero, Atom::Geq);
                    ref<Constraint> c2 = Atom::create(copy, zero, Atom::Lss);
                }
                //</Negar>
                ref<Rule> rule1 = Rule::create(lhs, rhs1, c1);
                ref<Rule> rule2 = Rule::create(lhs, rhs2, c2);
                m_blockRules.push_back(rule1);
                m_blockRules.push_back(rule2);
            }
            else
            {
                // mathematical integers of bounded integers with unsigned encoding
                ref<Term> rhs = Term::create(getEval(m_counter), getNewArgs(I, copy));
                ref<Rule> rule = Rule::create(lhs, rhs, Constraint::_true);
                m_blockRules.push_back(rule);
            }
        }
    }
}

void Converter::visitTruncInst(llvm::TruncInst &I)
{
    if (I.getType() == m_boolType)
    {
        return;
    }
    if (m_phase1)
    {
        m_vars.push_back(getVar(&I));
    }
    else
    {
        //<Negar>
        std::string leftVar = I.getName().str();
        std::string rightVar = I.getOperand(0)->getName().str();
        if (signednessInfo) {
            unsigned destinationBits = I.getType()->getIntegerBitWidth();
            std::cout << "v" << leftVar << " := extract(" << (destinationBits - 1) << ", 0, v" << rightVar << ");" << std::endl;
        }
        else {
            std::cout << "v" << leftVar << " := v" << rightVar << ";" << std::endl;
        }
        //</Negar>

        m_idMap.insert(std::make_pair(&I, m_counter));
        ref<Term> lhs = Term::create(getEval(m_counter), m_lhs);
        ref<Polynomial> val;
        if (m_boundedIntegers)
        {
            val = Polynomial::create(getNondef(&I));
        }
        else
        {
            val = getPolynomial(I.getOperand(0));
        }
        m_counter++;
        ref<Term> rhs = Term::create(getEval(m_counter), getNewArgs(I, val));
        ref<Rule> rule = Rule::create(lhs, rhs, Constraint::_true);
        m_blockRules.push_back(rule);
    }
}

bool Converter::isAssumeArg(llvm::ZExtInst &I)
{
    if (I.getOperand(0)->getType() == m_boolType)
    {
        if (I.getNumUses() != 1)
        {
            return false;
        }
#if LLVM_VERSION < VERSION(3, 5)
        llvm::User *user = *I.use_begin();
#else
        llvm::User *user = *I.user_begin();
#endif
        if (!llvm::isa<llvm::CallInst>(user))
        {
            return false;
        }
        llvm::CallSite callSite(llvm::cast<llvm::CallInst>(user));
        llvm::Function *calledFunction = callSite.getCalledFunction();
        if (calledFunction == NULL)
        {
            return false;
        }
        llvm::StringRef functionName = calledFunction->getName();
        if (functionName != "__kittel_assume")
        {
            return false;
        }
        return true;
    }
    return false;
}

std::set<std::string> Converter::getPhiVariables()
{
    return m_phiVars;
}

std::map<std::string, unsigned int> Converter::getBitwidthMap()
{
    return m_bitwidthMap;
}

std::set<std::string> Converter::getComplexityLHSs()
{
    return m_complexityLHSs;
}

//<Negar>
void Converter::visitBinaryOperator(llvm::BinaryOperator &binaryOp) {
    if (!m_phase1) {
        if (binaryOp.getOpcode() == llvm::Instruction::Shl || binaryOp.getOpcode() == llvm::Instruction::LShr || binaryOp.getOpcode() == llvm::Instruction::AShr) {
            std::string varName = binaryOp.getName().str();
            llvm::Value *firstOperand = binaryOp.getOperand(0);
            std::string firstOperandStr;
            if (auto *constInt = llvm::dyn_cast<llvm::ConstantInt>(firstOperand)) {
                firstOperandStr = std::to_string(constInt->getSExtValue());
            }
            else {
                firstOperandStr = "v" + firstOperand->getName().str();
            }
            llvm::Value *secondOperand = binaryOp.getOperand(1);
            std::string secondOperandStr;
            if (auto *constInt = llvm::dyn_cast<llvm::ConstantInt>(secondOperand)) {
                secondOperandStr = std::to_string(constInt->getSExtValue());
            }
            else {
                secondOperandStr = "v" + secondOperand->getName().str();
            }
            switch (binaryOp.getOpcode()) {
                case llvm::Instruction::Shl:
                    // Shift Left
                    std::cout << "v" << varName << " := shl(" << firstOperandStr << ", " << secondOperandStr << ");" << std::endl;
                    break;
                case llvm::Instruction::LShr:
                    // Unsigned Shift Right
                    std::cout << "v" << varName << " := lshr(" << firstOperandStr << ", " << secondOperandStr << ");" << std::endl;
                    break;
                case llvm::Instruction::AShr:
                    // Signed Shift Right
                    std::cout << "v" << varName << " := ashr(" << firstOperandStr << ", " << secondOperandStr << ");" << std::endl;
                    break;
                default:
                    break;
            }
        }
    }
}
//</Negar>

//<Negar>
void Converter::visitUIToFPInst(llvm::UIToFPInst &I) {
    if (!m_phase1) {
        std::string leftVar = I.getName().str();
        std::string rightVar = I.getOperand(0)->getName().str();
        unsigned bitWidth = I.getOperand(0)->getType()->getIntegerBitWidth();
        if (signednessInfo) {
            std::cout << "v" << leftVar << " := ubv2real(" << bitWidth << ", v" << rightVar << ");" << std::endl;
        }
        else {
            std::cout << "v" << leftVar << " := int2real(v" << rightVar << ");" << std::endl;
        }
    }
}
//</Negar>

//<Negar>
void Converter::visitSIToFPInst(llvm::SIToFPInst &I) {
    if(!m_phase1){
        std::string leftVar = I.getName().str();
        std::string rightVar = I.getOperand(0)->getName().str();
        unsigned bitWidth = I.getOperand(0)->getType()->getIntegerBitWidth();
        if (signednessInfo) {
            std::cout << "v" << leftVar << " := sbv2real(" << bitWidth << ", v" << rightVar << ");" << std::endl;
        }
        else {
            std::cout << "v" << leftVar << " := int2real(v" << rightVar << ");" << std::endl;
        }
    }
}
//</Negar>