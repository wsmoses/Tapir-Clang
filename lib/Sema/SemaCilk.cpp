//===--- SemaCilk.cpp - Semantic analysis for Cilk extensions -------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  This file implements semantic analysis for Cilk extensions.
//
//===----------------------------------------------------------------------===//

// #include "clang/AST/ExprCilk.h"
// #include "clang/AST/StmtCilk.h"
#include "llvm/ADT/SmallString.h"
#include "clang/AST/ParentMap.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Sema/Initialization.h"
#include "clang/Sema/Lookup.h"
#include "clang/Sema/Overload.h"
#include "clang/Sema/Scope.h"
#include "clang/Sema/SemaInternal.h"
#include "clang/Sema/Template.h"
using namespace clang;
using namespace sema;

namespace {
typedef llvm::SmallVectorImpl<VarDecl const *> VarDeclVec;

// This visitor looks for references to the loop control variable inside a
// _Cilk_for body.
class CilkForControlVarVisitor
  : public StmtVisitor<CilkForControlVarVisitor, bool> {
private:
  // This visitor looks for potential errors and warnings about the modification
  // of the loop control variable.
    class ControlVarUsageVisitor
      : public RecursiveASTVisitor<ControlVarUsageVisitor> {
    public:
      bool Error;

      // Constructor
      ControlVarUsageVisitor(Sema &S, DeclRefExpr *LCV, const ParentMap &P,
                             bool AddressOf)
          : Error(false), S(S), CurLCV(LCV), LCVDecl(CurLCV->getDecl()), PMap(P),
            AddressOf(AddressOf) {}

      // Check if the type is a pointer/reference to const data. If not, emit
      // diagnostic
      void CheckTypeAndDiagnose(QualType Ty, const SourceLocation &Loc,
                                unsigned DiagID, llvm::StringRef Param = "") {
        if ((Ty->isReferenceType() || (Ty->isPointerType() && AddressOf)) &&
            !Ty->getPointeeType().isConstQualified()) {
          if (!Param.empty())
            S.Diag(Loc, DiagID) << Param;
          else
            S.Diag(Loc, DiagID);
          S.Diag(LCVDecl->getLocation(),
                 diag::note_cilk_for_loop_control_var_declared_here);
        }
      }

      // Detect cases where the LCV is directly being assigned or an alias being
      // created
      bool VisitBinaryOperator(BinaryOperator *BO) {
              Expr *LHS =
                BO->getLHS()->IgnoreImpCasts()->IgnoreParenNoopCasts(S.Context);
              if (BO->isAssignmentOp()) {
                if (CurLCV == LHS) {
                  S.Diag(BO->getLocStart(),
                         diag::err_cilk_for_loop_modifies_control_var);
                  S.Diag(LCVDecl->getLocation(),
                         diag::note_cilk_for_loop_control_var_declared_here);
                  Error = true;
                } else {
                  CheckTypeAndDiagnose(BO->getType(), BO->getLocStart(),
                                       diag::warn_cilk_for_loop_control_var_aliased,
                                       LCVDecl->getName());
                }
              }
              return true;
      }

      // Detect cases of variable declarations that declare an alias to the LCV
      bool VisitVarDecl(VarDecl *VD) {
        CheckTypeAndDiagnose(VD->getType(), VD->getLocation(),
                             diag::warn_cilk_for_loop_control_var_aliased,
                             LCVDecl->getName());
        return true;
      }

      // Detect cases where a function call can modify the loop control variable
      bool VisitCallExpr(CallExpr *Call) {
        Stmt *P = PMap.getParent(CurLCV);

        // If we took the address of the LCV, ignore the &
        if (AddressOf)
          P = PMap.getParent(P);

        if (CastExpr *CE = dyn_cast<CastExpr>(P)) {
          // Look at the very top level cast to ignore any non-relevant casts
          CastExpr *TopLevelCast = CE;
          while (CastExpr *C = dyn_cast<CastExpr>(PMap.getParent(TopLevelCast))) {
            TopLevelCast = C;
          }

          CastKind Kind = TopLevelCast->getCastKind();
          QualType CastTy = TopLevelCast->getType();

          bool PtrOrRefConstQualified = false;
          if (AddressOf)
            PtrOrRefConstQualified = CastTy->getPointeeType().isConstQualified();
          else
            PtrOrRefConstQualified = CastTy.isConstQualified();

          if (Kind != CK_LValueToRValue &&
              !((Kind == CK_NoOp || Kind == CK_BitCast) &&
                PtrOrRefConstQualified)) {
            S.Diag(CurLCV->getLocation(),
                   diag::warn_cilk_for_loop_control_var_func);
            S.Diag(LCVDecl->getLocation(),
                   diag::note_cilk_for_loop_control_var_declared_here);
          }
        } else {
          // If its not a cast expression, we need to check which parameter(s)
          // can modify the loop control variable because in a rare case of the
          // comma operator where code like:
          //   int *p = (func(0), &i);
          // will generate a false positive in the 'func(0)' function call
          for (unsigned i = 0, len = Call->getNumArgs(); i != len; ++i) {
            Expr *Arg = Call->getArg(i)->IgnoreImpCasts()->IgnoreParenNoopCasts(
                S.Context);

            // Remove the & from the argument so that we can compare the argument
            // with the LCV to see if they are the same
            if (UnaryOperator *UO = dyn_cast<UnaryOperator>(Arg)) {
              if (UO->getOpcode() == UO_AddrOf)
                Arg = UO->getSubExpr();
            }
            if (Arg == CurLCV) {
              S.Diag(CurLCV->getLocation(),
                     diag::warn_cilk_for_loop_control_var_func);
              S.Diag(LCVDecl->getLocation(),
                     diag::note_cilk_for_loop_control_var_declared_here);
            }
          }
        }

        return true;
      }

      // Detect cases of ++/--.
      bool VisitUnaryOperator(UnaryOperator *UO) {
        if (UO->isIncrementDecrementOp() && UO->getSubExpr() == CurLCV) {
          S.Diag(UO->getLocStart(), diag::err_cilk_for_loop_modifies_control_var);
          S.Diag(LCVDecl->getLocation(),
                 diag::note_cilk_for_loop_control_var_declared_here);
          Error = true;
        }

        return true;
      }

    private:
      Sema &S;
      DeclRefExpr *CurLCV;      // Reference to the current loop control var
      const ValueDecl *LCVDecl; // The declaration of the current loop control var
      const ParentMap &PMap;
      bool AddressOf;
    };

public:
  bool Error;

  // Constructor
  CilkForControlVarVisitor(Sema &S, const ParentMap &PM, const VarDeclVec &LCVs)
      : Error(false), S(S), PMap(PM), LoopControlVarsInScope(LCVs) {}

  // Checks if the given DeclRefExpr is a reference to a loop control variable
  // in scope
  bool IsValidLoopControlVar(const DeclRefExpr *DeclRef) {
    VarDeclVec::const_iterator LCV =
      std::find(LoopControlVarsInScope.begin(), LoopControlVarsInScope.end(),
                DeclRef->getDecl());
    return LCV != LoopControlVarsInScope.end();
  }

  bool VisitDeclRefExpr(DeclRefExpr *DeclRef) {
    if (IsValidLoopControlVar(DeclRef)) {
      Stmt *P = PMap.getParentIgnoreParenImpCasts(DeclRef);
      bool AddressOf = false;
      // Check to see if the address of the loop control variable was taken and
      // strip off any casts from its parent.
      if (UnaryOperator *UO = dyn_cast_or_null<UnaryOperator>(P)) {
        if (UO->getOpcode() == UO_AddrOf) {
          AddressOf = true;
          Stmt *Parent = P;
          do {
            Parent = PMap.getParentIgnoreParenImpCasts(Parent);
          } while (Parent && isa<CastExpr>(Parent));
          if (Parent)
            P = Parent;
          // If the parent is a comma operator, get its parent to see if there
          // are any assignments.
          if (BinaryOperator *BO = dyn_cast<BinaryOperator>(P)) {
            if (BO->getOpcode() == BO_Comma)
              P = PMap.getParentIgnoreParenImpCasts(P);
          }
        }
      }
      // Use the usage visitor to analyze if the parent tries to modify the
      // loop control variable
      ControlVarUsageVisitor V(S, DeclRef, PMap, AddressOf);
      V.TraverseStmt(P);
      Error |= V.Error;
    }
    return true;
  }

  bool VisitStmt(Stmt *S) {
    for (auto *ST : S->children()) {
      if (ST)
        Visit(ST);
    }
    return true;
  }

private:
  Sema &S;
  const ParentMap &PMap;
  const VarDeclVec &LoopControlVarsInScope;
};

} // namespace

static bool CheckForInit(Sema &S, Stmt *Init, VarDecl *&ControlVar,
                         Expr *&ControlVarInit) {
  // Location of loop control variable/expression in the initializer
  SourceLocation InitLoc;

  if (DeclStmt *DS = dyn_cast<DeclStmt>(Init)) {
    // The initialization shall declare or initialize a single variable,
    // called the control variable.
    if (!DS->isSingleDecl()) {
      DeclStmt::decl_iterator DI = DS->decl_begin();
      ++DI;
      S.Diag((*DI)->getLocation(),
             diag::err_cilk_for_decl_multiple_variables);
      return false;
    }

    ControlVar = dyn_cast<VarDecl>(*DS->decl_begin());
    // Only allow VarDecls in the initializer
    if (!ControlVar) {
      S.Diag(Init->getLocStart(),
             diag::err_cilk_for_initializer_expected_decl)
        << Init->getSourceRange();
      return false;
    }

    // Ignore invalid decls.
    if (ControlVar->isInvalidDecl())
      return false;

    // The control variable shall be declared and initialized within the
    // initialization clause of the _Cilk_for loop.

    // A template type may have a default constructor.
    bool IsDependent = ControlVar->getType()->isDependentType();
    if (!IsDependent && !ControlVar->getInit()) {
      S.Diag(ControlVar->getLocation(),
             diag::err_cilk_for_control_variable_not_initialized);
      return false;
    }

    InitLoc = ControlVar->getLocation();
    ControlVarInit = ControlVar->getInit();
  } else {
    // In C++, the control variable shall be declared and initialized within
    // the initialization clause of the _Cilk_for loop.
    if (S.getLangOpts().CPlusPlus) {
      S.Diag(Init->getLocStart(),
             diag::err_cilk_for_initialization_must_be_decl);
      return false;
    }

    // In C only, the control variable may be previously declared, but if so
    // shall be reinitialized, i.e., assigned, in the initialization clause.
    BinaryOperator *Op = 0;
    if (Expr *E = dyn_cast<Expr>(Init)) {
      E = E->IgnoreParenNoopCasts(S.Context);
      Op = dyn_cast_or_null<BinaryOperator>(E);
    }

    if (!Op) {
      S.Diag(Init->getLocStart(),
             diag::err_cilk_for_control_variable_not_initialized);
      return false;
    }

    // The initialization shall declare or initialize a single variable,
    // called the control variable.
    if (Op->getOpcode() == BO_Comma) {
      S.Diag(Op->getRHS()->getExprLoc(),
             diag::err_cilk_for_init_multiple_variables);
      return false;
    }

    if (!Op->isAssignmentOp()) {
      S.Diag(Op->getLHS()->getExprLoc(),
             diag::err_cilk_for_control_variable_not_initialized)
        << Init->getSourceRange();
      return false;
    }

    // Get the decl for the LHS of the control variable initialization
    assert(Op->getLHS() && "BinaryOperator has no LHS!");
        DeclRefExpr *LHS =
          dyn_cast<DeclRefExpr>(Op->getLHS()->IgnoreParenNoopCasts(S.Context));
        if (!LHS) {
          S.Diag(Op->getLHS()->getExprLoc(),
                 diag::err_cilk_for_initializer_expected_variable)
            << Init->getSourceRange();
          return false;
        }

        // But, use the source location of the LHS for diagnostics
        InitLoc = LHS->getLocation();

        // Only a VarDecl may be used in the initializer
        ControlVar = dyn_cast<VarDecl>(LHS->getDecl());
        if (!ControlVar) {
          S.Diag(Op->getLHS()->getExprLoc(),
                 diag::err_cilk_for_initializer_expected_variable)
            << Init->getSourceRange();
          return false;
        }
        ControlVarInit = Op->getRHS();
  }

  bool IsDeclStmt = isa<DeclStmt>(Init);

  // No storage class may be specified for the variable within the
  // initialization clause.
  StorageClass SC = ControlVar->getStorageClass();
  if (SC != SC_None) {
    S.Diag(InitLoc,
           diag::err_cilk_for_control_variable_storage_class)
      << ControlVar->getStorageClassSpecifierString(SC);
    if (!IsDeclStmt)
      S.Diag(ControlVar->getLocation(), diag::note_local_variable_declared_here)
        << ControlVar->getIdentifier();
    return false;
  }

  // Don't allow non-local variables to be used as the control variable
  if (!ControlVar->isLocalVarDecl()) {
    S.Diag(InitLoc, diag::err_cilk_for_control_variable_not_local);
    return false;
  }

  QualType VarType = ControlVar->getType();

  // For decltype types, get the actual type
  const Type *VarTyPtr = VarType.getTypePtrOrNull();
  if (VarTyPtr && isa<DecltypeType>(VarTyPtr))
    VarType = cast<DecltypeType>(VarTyPtr)->getUnderlyingType();

  // The variable may not be const or volatile.
  // Assignment to const variables is checked before sema for cilk_for
  if (VarType.isVolatileQualified()) {
    S.Diag(InitLoc, diag::err_cilk_for_control_variable_qualifier)
      << "volatile";
    if (!IsDeclStmt)
      S.Diag(ControlVar->getLocation(), diag::note_local_variable_declared_here)
        << ControlVar->getIdentifier();
    return false;
  }

  // The variable shall have integral, pointer, or class type.  struct/class
  // types only allowed in C++. Defer the type check for a dependent type.
  if (!VarType->isDependentType()) {
    bool ValidType = false;
    if (S.getLangOpts().CPlusPlus &&
        (VarTyPtr->isClassType() || VarTyPtr->isStructureType() ||
         VarTyPtr->isUnionType()))
      ValidType = true;
    else if (VarTyPtr->isIntegralType(S.Context) || VarTyPtr->isPointerType())
      ValidType = true;

    if (!ValidType) {
      S.Diag(InitLoc, diag::err_cilk_for_control_variable_type);
      if (!IsDeclStmt)
        S.Diag(ControlVar->getLocation(),
               diag::note_local_variable_declared_here)
          << ControlVar->getIdentifier();
      return false;
    }
  }

  return true;
}

static bool ExtractForCondition(Sema &S, Expr *Cond, BinaryOperatorKind &CondOp,
                                SourceLocation &OpLoc, Expr *&LHS, Expr *&RHS) {
  if (BinaryOperator *BO = dyn_cast<BinaryOperator>(Cond)) {
    CondOp = BO->getOpcode();
    OpLoc = BO->getOperatorLoc();
    LHS = BO->getLHS();
    RHS = BO->getRHS();
    return true;
  } else if (CXXOperatorCallExpr *OO = dyn_cast<CXXOperatorCallExpr>(Cond)) {
    CondOp = BinaryOperator::getOverloadedOpcode(OO->getOperator());
    if (OO->getNumArgs() == 2) {
      OpLoc = OO->getOperatorLoc();
      LHS = OO->getArg(0);
      RHS = OO->getArg(1);
      return true;
    }
  } else if (ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(Cond)) {
    if (ICE->getCastKind() == CK_UserDefinedConversion) {
      Expr *From = ICE->getSubExprAsWritten();
      // Note: flags copied from TryContextuallyConvertToBool
      ImplicitConversionSequence ICS =
        S.TryImplicitConversion(From, ICE->getType(),
                                /*SuppressUserConversions=*/false,
                                /*AllowExplicit=*/true,
                                /*InOverloadResolution=*/false,
                                /*CStyle=*/false,
                                /*AllowObjCWritebackConversion=*/false);
      assert(!ICS.isBad() &&
             ICS.getKind() ==
             ImplicitConversionSequence::UserDefinedConversion);
      S.Diag(Cond->getExprLoc(), diag::warn_cilk_for_cond_user_defined_conv)
        << From->getType() << ICE->getType() << Cond->getSourceRange();
      FunctionDecl *FD =
        ICS.UserDefined.ConversionFunction->getCanonicalDecl();
      S.Diag(FD->getLocation(), diag::note_cilk_for_conversion_here)
        << ICE->getType();
    }
    Cond = ICE->getSubExpr();
    return ExtractForCondition(S, Cond, CondOp, OpLoc, LHS, RHS);
  } else if (CXXMemberCallExpr *MC = dyn_cast<CXXMemberCallExpr>(Cond)) {
    CXXMethodDecl *MD = MC->getMethodDecl();
    if (isa<CXXConversionDecl>(MD))
      return ExtractForCondition(S, MC->getImplicitObjectArgument(), CondOp,
                                 OpLoc, LHS, RHS);
  } else if (CXXBindTemporaryExpr *BT = dyn_cast<CXXBindTemporaryExpr>(Cond)) {
    return ExtractForCondition(S, BT->getSubExpr(), CondOp, OpLoc, LHS, RHS);
  } else if (ExprWithCleanups *EWC = dyn_cast<ExprWithCleanups>(Cond))
    return ExtractForCondition(S, EWC->getSubExpr(), CondOp, OpLoc, LHS, RHS);

  S.Diag(Cond->getExprLoc(), diag::err_cilk_for_invalid_cond_expr)
    << Cond->getSourceRange();
  return false;
}

static bool IsControlVarRef(Expr *E, const VarDecl *ControlVar) {
  // Only ignore very basic casts and this allows us to distinguish
  //
  // struct Int {
  //  Int();
  //  operator int&();
  // };
  //
  // _Cilk_for (Int i; i.opertor int&() < 10; ++i);
  //
  // and
  //
  // _Cilk_for (Int i; i < 10; ++i);
  //
  // The first is a member function call and the second is also member function
  // call but associated with a user defined conversion cast.
  //
  E = E->IgnoreParenLValueCasts();

  if (CXXConstructExpr *C = dyn_cast<CXXConstructExpr>(E)) {
    if (C->getConstructor()->isConvertingConstructor(false))
      return IsControlVarRef(C->getArg(0), ControlVar);
  } else if (CXXBindTemporaryExpr *BE = dyn_cast<CXXBindTemporaryExpr>(E)) {
    return IsControlVarRef(BE->getSubExpr(), ControlVar);
  } else if (ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(E)) {
    // Apply recursively with the subexpression written in the source.
    return IsControlVarRef(ICE->getSubExprAsWritten(), ControlVar);
  } else if (DeclRefExpr *DR = dyn_cast<DeclRefExpr>(E))
    if (DR->getDecl() == ControlVar)
      return true;

  return false;
}

static bool CanonicalizeForCondOperands(Sema &S, const VarDecl *ControlVar,
                                        Expr *Cond, Expr *&LHS, Expr *&RHS,
                                        int &Direction, unsigned CondDiagError,
                                        unsigned CondDiagNote) {

  // The condition shall have one of the following two forms:
  //   var OP shift-expression
  //   shift-expression OP var
  // where var is the control variable, optionally enclosed in parentheses.
  if (IsControlVarRef(LHS, ControlVar))
    return true;

  if (IsControlVarRef(RHS, ControlVar)) {
    std::swap(LHS, RHS);
    Direction = -Direction;
    return true;
  }

  S.Diag(Cond->getLocStart(), CondDiagError) << ControlVar
                                             << Cond->getSourceRange();
  S.Diag(Cond->getLocStart(), CondDiagNote) << ControlVar;
  return false;
}

static void CheckForCondition(Sema &S, VarDecl *ControlVar, Expr *Cond,
                              Expr *&Limit, int &Direction,
                              BinaryOperatorKind &Opcode) {
  SourceLocation OpLoc;
  Expr *LHS = 0;
  Expr *RHS = 0;

  Cond = Cond->IgnoreParens();
  if (!ExtractForCondition(S, Cond, Opcode, OpLoc, LHS, RHS))
    return;

  // The operator denoted OP shall be one of !=, <=, <, >=, or >.
  switch (Opcode) {
  case BO_NE:
    Direction = 0;
    break;
  case BO_LT:
  case BO_LE:
    Direction = 1;
    break;
  case BO_GT:
  case BO_GE:
    Direction = -1;
    break;
  default:
    S.Diag(OpLoc, diag::err_cilk_for_invalid_cond_operator);
    return;
  }
  unsigned CondDiagError = diag::err_cilk_for_cond_test_control_var;
  unsigned CondDiagNote = diag::note_cilk_for_cond_allowed;
  if (!CanonicalizeForCondOperands(S, ControlVar, Cond, LHS, RHS, Direction,
                                   CondDiagError, CondDiagNote))
    return;

  Limit = RHS;
}

static bool isAdditiveAssignOp(BinaryOperator::Opcode Opc) {
  return Opc == BO_AddAssign || Opc == BO_SubAssign;
}

static bool IsValidForIncrement(Sema &S, Expr *Increment,
                                const VarDecl *ControlVar,
                                bool &HasConstantIncrement,
                                llvm::APSInt &Stride, Expr *&StrideExpr,
                                SourceLocation &RHSLoc) {
  Increment = Increment->IgnoreParens();
  if (ExprWithCleanups *E = dyn_cast<ExprWithCleanups>(Increment))
    Increment = E->getSubExpr();
  if (CXXBindTemporaryExpr *E = dyn_cast<CXXBindTemporaryExpr>(Increment))
    Increment = E->getSubExpr();

  // Simple increment or decrement -- always OK
  if (UnaryOperator *U = dyn_cast<UnaryOperator>(Increment)) {
    if (!IsControlVarRef(U->getSubExpr(), ControlVar)) {
      S.Diag(U->getSubExpr()->getExprLoc(),
             diag::err_cilk_for_increment_not_control_var)
        << ControlVar;
      return false;
    }

    if (U->isIncrementDecrementOp()) {
      HasConstantIncrement = true;
      Stride = (U->isIncrementOp() ? 1 : -1);
      StrideExpr = S.ActOnIntegerConstant(Increment->getExprLoc(), 1).get();
      if (U->isDecrementOp())
        StrideExpr = S.BuildUnaryOp(S.getCurScope(), Increment->getExprLoc(),
                                    UO_Minus, StrideExpr).get();
      return true;
    }
  }

  // In the case of += or -=, whether built-in or overloaded, we need to check
  // the type of the right-hand side. In that case, RHS will be set to a
  // non-null value.
  Expr *RHS = 0;
  // Direction is 1 if the operator is +=, -1 if it is -=
  int Direction = 0;
  StringRef OperatorName;

  if (CXXOperatorCallExpr *C = dyn_cast<CXXOperatorCallExpr>(Increment)) {
    OverloadedOperatorKind Overload = C->getOperator();

    if (!IsControlVarRef(C->getArg(0), ControlVar)) {
      S.Diag(C->getArg(0)->getExprLoc(),
             diag::err_cilk_for_increment_not_control_var)
        << ControlVar;
      return false;
    }

    // operator++() or operator--() -- always OK
    if (Overload == OO_PlusPlus || Overload == OO_MinusMinus) {
      HasConstantIncrement = true;
      Stride = (Overload == OO_PlusPlus ? 1 : -1);
      StrideExpr = S.ActOnIntegerConstant(Increment->getExprLoc(), 1).get();
      if (Overload == OO_MinusMinus)
        StrideExpr = S.BuildUnaryOp(S.getCurScope(), Increment->getExprLoc(),
                                    UO_Minus, StrideExpr).get();
      return true;
    }

    // operator+=() or operator-=() -- defer checking of the RHS type
    if (Overload == OO_PlusEqual || Overload == OO_MinusEqual) {
      RHS = C->getArg(1);
      OperatorName = (Overload == OO_PlusEqual ? "+=" : "-=");
      Direction = Overload == OO_PlusEqual ? 1 : -1;
    }
  }

  if (BinaryOperator *B = dyn_cast<CompoundAssignOperator>(Increment)) {
    if (!IsControlVarRef(B->getLHS(), ControlVar)) {
      S.Diag(B->getLHS()->getExprLoc(),
             diag::err_cilk_for_increment_not_control_var)
        << ControlVar;
      return false;
    }

    // += or -= -- defer checking of the RHS type
    if (isAdditiveAssignOp(B->getOpcode())) {
      RHS = B->getRHS();
      OperatorName = B->getOpcodeStr();
      Direction = B->getOpcode() == BO_AddAssign ? 1 : -1;
    }
  }

  // If RHS is non-null, it's a += or -=, either built-in or overloaded.
  // We need to check that the RHS has the correct type.
  if (RHS) {
    if (RHS->isTypeDependent())
      return true;

    if (!RHS->getType()->isIntegralOrEnumerationType()) {
      S.Diag(Increment->getExprLoc(),
             diag::err_cilk_for_invalid_increment_rhs)
        << OperatorName;
      return false;
    }

    // Handle the case like 'RHS = sizeof(T)', which is not type dependent
    // but value dependent.
    if (RHS->isValueDependent())
      return true;

    HasConstantIncrement = RHS->EvaluateAsInt(Stride, S.Context);
    StrideExpr = RHS;
    if (Direction == -1) {
      Stride = -Stride;
      StrideExpr = S.BuildUnaryOp(S.getCurScope(), Increment->getExprLoc(),
                                  UO_Minus, StrideExpr).get();
    }
    RHSLoc = RHS->getExprLoc();
    return true;
  }

  // If we reached this point, the basic form is invalid. Issue a diagnostic.
  S.Diag(Increment->getExprLoc(), diag::err_cilk_for_invalid_increment);
  return false;
}

ExprResult Sema::CalculateCilkForLoopCount(SourceLocation CilkForLoc,
                                           Expr *Span, Expr *Increment,
                                           Expr *StrideExpr, int Dir,
                                           BinaryOperatorKind Opcode) {
  // Generate the loop count expression according to the following:
  // ===========================================================================
  // |     Condition syntax             |       Loop count                     |
  // ===========================================================================
  // | if var < limit or limit > var    | (span-1)/stride + 1                  |
  // ---------------------------------------------------------------------------
  // | if var > limit or limit < var    | (span-1)/-stride + 1                 |
  // ---------------------------------------------------------------------------
  // | if var <= limit or limit >= var  | span/stride + 1                      |
  // ---------------------------------------------------------------------------
  // | if var >= limit or limit <= var  | span/-stride + 1                     |
  // ---------------------------------------------------------------------------
  // | if var != limit or limit != var  | if stride is positive,               |
  // |                                  |            span/stride               |
  // |                                  | otherwise, span/-stride              |
  // |                                  | We don't need "+(stride-1)" for the  |
  // |                                  | span in this case since the incr/decr|
  // |                                  | operator should add up to the        |
  // |                                  | limit exactly for a valid loop.      |
  // ---------------------------------------------------------------------------
  // Build "-stride"
  Expr *NegativeStride = BuildUnaryOp(getCurScope(), Increment->getExprLoc(),
                                      UO_Minus, StrideExpr).get();

  ExprResult LoopCount;
  if (Opcode == BO_NE) {
    if (StrideExpr->getType()->isSignedIntegerOrEnumerationType()) {
      // Build "stride<0"
      Expr *StrideLessThanZero =
        BuildBinOp(getCurScope(), CilkForLoc, BO_LT, StrideExpr,
                   ActOnIntegerConstant(CilkForLoc, 0).get()).get();
      // Build "(stride<0)?-stride:stride"
      ExprResult StrideCondExpr =
        ActOnConditionalOp(CilkForLoc, CilkForLoc, StrideLessThanZero,
                           NegativeStride, StrideExpr);
      // Build "-span"
      Expr *NegativeSpan =
        BuildUnaryOp(getCurScope(), CilkForLoc, UO_Minus, Span).get();

      // Updating span to be "(stride<0)?-span:span"
      Span = ActOnConditionalOp(CilkForLoc, CilkForLoc, StrideLessThanZero,
                                NegativeSpan, Span).get();
      // Build "span/(stride<0)?-stride:stride"
      LoopCount = BuildBinOp(getCurScope(), CilkForLoc, BO_Div, Span,
                             StrideCondExpr.get());
    } else
      // Unsigned, no need to compare - Build "span/stride"
      LoopCount =
        BuildBinOp(getCurScope(), CilkForLoc, BO_Div, Span, StrideExpr);

  } else {
    if (Opcode == BO_LT || Opcode == BO_GT)
      // Updating span to be "span-1"
      Span =
        CreateBuiltinBinOp(CilkForLoc, BO_Sub, Span,
                           ActOnIntegerConstant(CilkForLoc, 1).get()).get();

    // Build "span/stride" if Dir==1, otherwise "span/-stride"
    LoopCount = BuildBinOp(getCurScope(), CilkForLoc, BO_Div, Span,
                           (Dir == 1) ? StrideExpr : NegativeStride);

    // Build "span/stride + 1"
    LoopCount = BuildBinOp(getCurScope(), CilkForLoc, BO_Add, LoopCount.get(),
                           ActOnIntegerConstant(CilkForLoc, 1).get());
  }

  QualType LoopCountExprType = LoopCount.get()->getType();
  QualType LoopCountType = Context.UnsignedLongLongTy;
  // Loop count should be either u32 or u64 in Cilk Plus.
  if (Context.getTypeSize(LoopCountExprType) > 64)
    Diag(CilkForLoc, diag::warn_cilk_for_loop_count_downcast)
      << LoopCountExprType << LoopCountType;
  else if (Context.getTypeSize(LoopCountExprType) <= 32)
    LoopCountType = Context.UnsignedIntTy;

  // Implicitly casting LoopCount to u32/u64.
  return ImpCastExprToType(LoopCount.get(), LoopCountType, CK_IntegralCast);
}

// StmtResult Sema::ActOnCilkForGrainsizePragma(Expr *GrainsizeExpr, Stmt *CilkFor,
//                                              SourceLocation LocStart) {
//   SourceLocation GrainSizeStart = GrainsizeExpr->getLocStart();

//   // Negative grainsize has unspecified behavior and is reserved for future
//   // extensions.
//   llvm::APSInt Result;
//   if (GrainsizeExpr->EvaluateAsInt(Result, Context))
//     if (Result.isNegative()) {
//       Diag(GrainSizeStart, diag::err_cilk_for_grainsize_negative);
//       return StmtError();
//     }

//   // Check if the result of the Grainsize expression is convertible to signed
//   // int.
//   QualType GrainsizeTy = Context.IntTy;
//   VarDecl *Grainsize = VarDecl::Create(
//       Context, CurContext, GrainSizeStart, GrainSizeStart, 0, GrainsizeTy,
//       Context.getTrivialTypeSourceInfo(GrainsizeTy, GrainSizeStart), SC_None);

//   AddInitializerToDecl(Grainsize, GrainsizeExpr, true, false);
//   if (Grainsize->isInvalidDecl()) {
//     Context.Deallocate(reinterpret_cast<void *>(Grainsize));
//     Diag(GrainSizeStart, diag::note_cilk_for_grainsize_conversion)
//       << GrainsizeTy;
//     return StmtError();
//   }

//   GrainsizeExpr = Grainsize->getInit();
//   Context.Deallocate(reinterpret_cast<void *>(Grainsize));
//   return new (Context) CilkForGrainsizeStmt(GrainsizeExpr, CilkFor, LocStart);
// }

static void CheckForSignedUnsignedWraparounds(
    const VarDecl *ControlVar, const Expr *ControlVarInit, const Expr *Limit,
    Sema &S, int CondDirection, llvm::APSInt Stride, const Expr *StrideExpr) {
  llvm::APSInt InitVal;
  llvm::APSInt LimitVal;
  if (!ControlVar->getType()->isDependentType() &&
      !ControlVarInit->isInstantiationDependent() &&
      !Limit->isInstantiationDependent()) {
    if (ControlVarInit->isIntegerConstantExpr(InitVal, S.Context) &&
        Limit->isIntegerConstantExpr(LimitVal, S.Context) &&
        CondDirection == 0) {
      // Make InitVal, LimitVal, and Stride have the same width
      // so that they can be compared.
      unsigned MaxBitWidth = std::max(
          std::max(InitVal.getMinSignedBits(), LimitVal.getMinSignedBits()),
          Stride.getMinSignedBits());
      InitVal = InitVal.sextOrTrunc(MaxBitWidth);
      LimitVal = LimitVal.sextOrTrunc(MaxBitWidth);
      Stride = Stride.sextOrTrunc(MaxBitWidth);
      InitVal.setIsSigned(true);
      LimitVal.setIsSigned(true);
      Stride.setIsSigned(true);

      const char *StrideSign = (Stride.isNegative() ? "negative" : "positive");
      const char *SignedUnsigned =
        (ControlVar->getType()->isUnsignedIntegerOrEnumerationType()
         ? "unsigned"
         : "signed");
      if ((Stride.isNegative() && InitVal < LimitVal) ||
          (Stride.isStrictlyPositive() && InitVal > LimitVal)) {
        S.Diag(StrideExpr->getExprLoc(), diag::warn_cilk_for_wraparound)
          << StrideSign << SignedUnsigned;
        S.Diag(StrideExpr->getExprLoc(),
               diag::note_cilk_for_wraparound_undefined);
      } else if (StrideExpr->isIntegerConstantExpr(S.Context)) {
        if (LimitVal % Stride != 0) {
          S.Diag(StrideExpr->getExprLoc(), diag::warn_cilk_for_wraparound)
            << StrideSign << SignedUnsigned;
          S.Diag(StrideExpr->getExprLoc(),
                 diag::note_cilk_for_wraparound_undefined);
        }
      }
    }
  }
}

bool Sema::CheckIfBodyModifiesLoopControlVar(Stmt *Body) {
  assert(!FunctionScopes.empty() && "Must be inside a _Cilk_for scope");

  llvm::SmallVector<VarDecl const *, 1> LoopControlVarsInScope;

  // Store all the _Cilk_for loop control vars upto the top most _Cilk_for
  for (SmallVectorImpl<sema::FunctionScopeInfo *>::reverse_iterator
         I = FunctionScopes.rbegin(),
         E = FunctionScopes.rend();
       I != E; ++I) {
    if (CilkForScopeInfo *CSI = dyn_cast<CilkForScopeInfo>(*I)) {
      LoopControlVarsInScope.push_back(CSI->LoopControlVar);
    }
  }

  ParentMap PMap(Body);
  CilkForControlVarVisitor V(*this, PMap, LoopControlVarsInScope);
  V.Visit(Body);

  return V.Error;
}

static bool CheckForIncrement(Sema &S, Expr *Increment, const Expr *Limit,
                              const VarDecl *ControlVar,
                              const Expr *ControlVarInit, int CondDirection,
                              Expr *&StrideExpr) {
  // Check increment
  // For dependent types since we can't get the actual type, we default to a
  // 64bit signed type.
  llvm::APSInt Stride(64, true);
  // Otherwise, stride should be the same type as the control var. This only
  // matters because of the computation we do with the value of the loop limit
  // later.
  if (!ControlVar->getType()->isDependentType())
    Stride = llvm::APSInt(
        S.Context.getTypeSize(ControlVar->getType()),
        ControlVar->getType()->isUnsignedIntegerOrEnumerationType());

  bool HasConstantIncrement = false;
  SourceLocation IncrementRHSLoc;
  if (!IsValidForIncrement(S, Increment, ControlVar, HasConstantIncrement,
                           Stride, StrideExpr, IncrementRHSLoc))
    return false;

  // Check consistency between loop condition and increment only if the
  // increment amount is known at compile-time.
  if (HasConstantIncrement) {
    if (!Stride) {
      S.Diag(IncrementRHSLoc, diag::err_cilk_for_increment_zero);
      return false;
    }

    if ((CondDirection > 0 && Stride.isNegative()) ||
        (CondDirection < 0 && Stride.isStrictlyPositive())) {
      S.Diag(Increment->getExprLoc(),
             diag::err_cilk_for_increment_inconsistent)
        << (CondDirection > 0);
      S.Diag(Increment->getExprLoc(), diag::note_constant_stride)
        << Stride.toString(10, true)
        << SourceRange(Increment->getExprLoc(), Increment->getLocEnd());
      return false;
    }

    // For simd, do not check unsigned wrap around here, since OpenMP does not
    // support operation '!=' for the condition.
    CheckForSignedUnsignedWraparounds(ControlVar, ControlVarInit, Limit, S,
                                      CondDirection, Stride, StrideExpr);
  }

  return true;
}

// Find the loop control variable. Returns null if not found.
static const VarDecl *getLoopControlVariable(Sema &S, StmtResult InitStmt) {
  if (InitStmt.isInvalid())
    return nullptr;

  Stmt *Init = InitStmt.get();

  // No initialization.
  if (!Init)
    return nullptr;

  const VarDecl *Candidate = nullptr;

  // Initialization is a declaration statement.
  if (DeclStmt *DS = dyn_cast<DeclStmt>(Init)) {
    if (!DS->isSingleDecl())
      return nullptr;

    if (VarDecl *Var = dyn_cast<VarDecl>(DS->getSingleDecl()))
      Candidate = Var;
  } else {
    // Initialization is an expression.
    BinaryOperator *Op = 0;
    if (Expr *E = dyn_cast<Expr>(Init)) {
      E = E->IgnoreParenNoopCasts(S.Context);
      Op = dyn_cast<BinaryOperator>(E);
    }

    if (!Op || !Op->isAssignmentOp())
      return nullptr;

    Expr *E = Op->getLHS();
    if (!E)
      return nullptr;

    E = E->IgnoreParenNoopCasts(S.Context);
    DeclRefExpr *LHS = dyn_cast<DeclRefExpr>(E);
    if (!LHS)
      return nullptr;

    if (VarDecl *Var = dyn_cast<VarDecl>(LHS->getDecl()))
      Candidate = Var;
  }

  // Only local variables can be a loop control variable.
  if (Candidate && Candidate->isLocalVarDecl())
    return Candidate;

  // Cannot find the loop control variable.
  return nullptr;
}

void Sema::ActOnStartOfCilkForStmt(SourceLocation CilkForLoc, Scope *CurScope,
                                   StmtResult FirstPart) {

  CapturedDecl *CD = nullptr;
  RecordDecl *RD = CreateCapturedStmtRecordDecl(CD, CilkForLoc, /*NumArgs*/ 3);

  // Build the context parameter
  DeclContext *DC = CapturedDecl::castToDeclContext(CD);
  IdentifierInfo *ParamName = &Context.Idents.get("__context");
  QualType ParamType = Context.getPointerType(Context.getTagDeclType(RD));
  ImplicitParamDecl *Param
    = ImplicitParamDecl::Create(Context, DC, CilkForLoc, ParamName, ParamType,
                                ImplicitParamDecl::Other);
  DC->addDecl(Param);

  CD->setContextParam(0, Param);

  const VarDecl *VD = getLoopControlVariable(*this, FirstPart);
  PushCilkForScope(CurScope, CD, RD, VD, CilkForLoc);

  // Push a compound scope for the body. This is needed for the case
  //
  // _Cilk_for (...)
  //   _Cilk_spawn foo();
  //
  PushCompoundScope();

  if (CurScope)
    PushDeclContext(CurScope, CD);
  else
    CurContext = CD;

  PushExpressionEvaluationContext(
      ExpressionEvaluationContext::PotentiallyEvaluated);
}

namespace {

bool extendsLifetimeOfTemporary(const VarDecl *VD) {
  // Attempt to determine whether this declaration lifetime-extends a
  // temporary.
  //
  // FIXME: This is incorrect. Non-reference declarations can lifetime-extend
  // temporaries, and a single declaration can extend multiple temporaries.
  // We should look at the storage duration on each nested
  // MaterializeTemporaryExpr instead.
  //
  // Commit 49bab4c0046e8300c79e79b7ca9a479696c7e87a
  //
  const Expr *Init = VD->getInit();
  if (!Init)
    return false;
  if (const ExprWithCleanups *EWC = dyn_cast<ExprWithCleanups>(Init))
    Init = EWC->getSubExpr();
  return isa<MaterializeTemporaryExpr>(Init);
}

}

static bool CommonActOnForStmt(Sema &S, SourceLocation ForLoc,
                               SourceLocation LParenLoc, Stmt *First,
                               Expr *Cond, Expr *Increment,
                               SourceLocation RParenLoc, Stmt *Body,
                               ExprResult &LoopCount, Expr *&StrideExpr,
                               ExprResult &Span) {
  assert(First && "expected init");
  assert(Cond && "expected cond");
  assert(Increment && "expected increment");

  // Check loop initializer and get control variable and its initialization
  VarDecl *ControlVar = nullptr;
  Expr *ControlVarInit = nullptr;
  if (!CheckForInit(S, First, ControlVar, ControlVarInit))
    return false;

  // Check loop condition
  S.CheckForLoopConditionalStatement(Cond, Increment, Body);

  Expr *Limit = nullptr;
  int CondDirection = 0;
  BinaryOperatorKind Opcode;
  CheckForCondition(S, ControlVar, Cond, Limit, CondDirection, Opcode);
  if (!Limit)
    return false;

  // Remove any implicit AST node introduced by semantic analysis.
  Limit = Limit->getSubExprAsWritten();

  if (!CheckForIncrement(S, Increment, Limit, ControlVar, ControlVarInit,
                         CondDirection, StrideExpr))
    return false;

  if (!S.CurContext->isDependentContext()) {
    StrideExpr = StrideExpr->getSubExprAsWritten();

    // Push an evaluation context in case span needs cleanups.
    EnterExpressionEvaluationContext EvalContext(
        S, Sema::ExpressionEvaluationContext::PotentiallyEvaluated);

    // Build end - begin
    Expr *Begin = S.BuildDeclRefExpr(
        ControlVar, ControlVar->getType().getNonReferenceType(),
        VK_LValue, ControlVar->getLocation()).get();
    Expr *End = Limit;
    if (CondDirection < 0)
      std::swap(Begin, End);

    Span = S.BuildBinOp(S.getCurScope(), ForLoc, BO_Sub, End, Begin);

    if (Span.isInvalid()) {
      // error getting operator-()
      S.Diag(ForLoc, diag::err_cilk_for_difference_ill_formed);
      S.Diag(Begin->getLocStart(), diag::note_cilk_for_begin_expr)
        << Begin->getSourceRange();
      S.Diag(End->getLocStart(), diag::note_cilk_for_end_expr)
        << End->getSourceRange();
      return false;
    }

    if (!Span.get()->getType()->isIntegralOrEnumerationType()) {
      // non-integral type
      S.Diag(ForLoc, diag::err_non_integral_cilk_for_difference_type)
        << Span.get()->getType();
      S.Diag(Begin->getLocStart(), diag::note_cilk_for_begin_expr)
        << Begin->getSourceRange();
      S.Diag(End->getLocStart(), diag::note_cilk_for_end_expr)
        << End->getSourceRange();
      return false;
    }

    assert(Span.get() && "missing span for cilk for loop count");
    LoopCount = S.CalculateCilkForLoopCount(ForLoc, Span.get(), Increment,
                                            StrideExpr, CondDirection, Opcode);

    // The loop count calculation may require cleanups in three cases:
    // a) building the binary operator- requires a cleanup
    // b) the Limit expression contains a temporary with a destructor
    // c) the Stride expression contains a temporary with a destructor
    //
    // The case (a) is handled above in BuildBinOp, but (b,c) must be checked
    // explicitly, since Limit and Stride were built in a different evaluation
    // context.
    if (Limit->hasNonTrivialCall(S.Context) ||
        StrideExpr->hasNonTrivialCall(S.Context))
      S.Cleanup.setExprNeedsCleanups(true);

    // LoopCount = S.MakeFullExpr(LoopCount.get()).get();
    LoopCount = S.MaybeCreateExprWithCleanups(LoopCount);
  }

  S.DiagnoseUnusedExprResult(First);
  S.DiagnoseUnusedExprResult(Increment);
  S.DiagnoseUnusedExprResult(Body);
  if (isa<NullStmt>(Body))
    S.getCurCompoundScopeSkipCilkFor().setHasEmptyLoopBodies();

  return true;
}

StmtResult Sema::ActOnCilkForStmt(SourceLocation CilkForLoc,
                                  SourceLocation LParenLoc, Stmt *First,
                                  ConditionResult Second, FullExprArg Third,
                                  SourceLocation RParenLoc, Stmt *Body) {
  ExprResult LoopCount, Span;
  Expr *StrideExpr = nullptr;
  if (!CommonActOnForStmt(*this, CilkForLoc, LParenLoc, First, Second.get().second,
                          Third.get(), RParenLoc, Body, LoopCount, StrideExpr,
                          Span))
    return StmtError();
  return BuildCilkForStmt(CilkForLoc, LParenLoc, First, Second.get().second,
                          Third.get(), RParenLoc, Body, LoopCount.get(),
                          StrideExpr,
                          Span.isUsable() ? Span.get()->getType() : QualType());
}

static void ActOnForStmtError(Sema &S, RecordDecl *Record) {
  S.DiscardCleanupsInEvaluationContext();
  S.PopExpressionEvaluationContext();

  Record->setInvalidDecl();

  // SmallVector<Decl *, 4> Fields;
  // for (RecordDecl::field_iterator I = Record->field_begin(),
  //        E = Record->field_end();
  //      I != E; ++I)
  //   Fields.push_back(*I);
  SmallVector<Decl *, 4> Fields(Record->fields());
  S.ActOnFields(/*Scope=*/nullptr, Record->getLocation(), Record, Fields,
                SourceLocation(), SourceLocation(), /*AttributeList=*/nullptr);

  S.PopDeclContext();
  // Pop the compound scope we inserted implicitly.
  S.PopCompoundScope();
  S.PopFunctionScopeInfo();
}

void Sema::ActOnCilkForStmtError() {
  ActOnForStmtError(*this, getCurCilkFor()->TheRecordDecl);
}

static bool CheckUnsupportedCall(Sema &S, CallExpr *Call) {
  assert(Call->isCilkSpawnCall() && "Cilk spawn expected");

  SourceLocation SpawnLoc = Call->getCilkSpawnLoc();
  if (isa<UserDefinedLiteral>(Call) || isa<CUDAKernelCallExpr>(Call)) {
    S.Diag(SpawnLoc, diag::err_cannot_spawn_function);
    return false;
  }

  return true;
}

static bool CheckSpawnCallExpr(Sema &S, Expr *E, SourceLocation SpawnLoc) {
  // Do not need to check an already checked spawn.
  if (isa<CilkSpawnExpr>(E))
    return true;

  E = E->IgnoreImplicitForCilkSpawn();
  Expr *RHS = nullptr;

  // x = _Cilk_spawn f(); // x is a non-class object.
  if (BinaryOperator *B = dyn_cast<BinaryOperator>(E)) {
    if (B->getOpcode() != BO_Assign) {
      S.Diag(SpawnLoc, diag::err_spawn_not_whole_expr) << E->getSourceRange();
      return false;
    }
    RHS = B->getRHS();
  } else {
    CallExpr *Call = dyn_cast<CallExpr>(E);

    // Not a call.
    if (!Call) {
      S.Diag(SpawnLoc, diag::err_spawn_not_whole_expr) << E->getSourceRange();
      return false;
    }

    // This is a spawn call.
    if (Call->isCilkSpawnCall())
      return CheckUnsupportedCall(S, Call);

    CXXOperatorCallExpr *OC = dyn_cast<CXXOperatorCallExpr>(E);
    if (!OC || (OC->getOperator() != OO_Equal)) {
      S.Diag(SpawnLoc, diag::err_spawn_not_whole_expr) << E->getSourceRange();
      return false;
    }
    // x = _Cilk_spawn f(); // x is a class object.
    RHS = OC->getArg(1);
  }

  // Up to this point, RHS is expected to be '_Cilk_spawn f()'.
  RHS = RHS->IgnoreImplicitForCilkSpawn();

  CallExpr *Call = dyn_cast<CallExpr>(RHS);
  if (!Call || !Call->isCilkSpawnCall()) {
    S.Diag(SpawnLoc, diag::err_spawn_not_whole_expr) << E->getSourceRange();
    return false;
  }

  return CheckUnsupportedCall(S, Call);
}

bool Sema::DiagCilkSpawnFullExpr(Expr *EE) {
  bool IsValid = true;
  assert(EE && !CilkSpawnCalls.empty() && "Cilk spawn expected");
  SourceLocation SpawnLoc = (*CilkSpawnCalls.rbegin())->getCilkSpawnLoc();
  if (CilkSpawnCalls.size() == 1) {
    // Only a single Cilk spawn in this expression; check if it is
    // in a proper place:
    //
    // (1) _Cilk_spawn f()
    //
    // (2) x = _Cilk_spawn f()
    //
    // where the second form may be "operator=" call.
    IsValid = CheckSpawnCallExpr(*this, EE, SpawnLoc);
  } else {
    SmallVectorImpl<CallExpr *>::reverse_iterator I = CilkSpawnCalls.rbegin();
    SmallVectorImpl<CallExpr *>::reverse_iterator E = CilkSpawnCalls.rend();

    IsValid = false;
    Diag(SpawnLoc, diag::err_multiple_spawns) << EE->getSourceRange();
    // Starting from the second spawn, emit a note.
    for (++I; I != E; ++I)
      Diag((*I)->getCilkSpawnLoc(), diag::note_multiple_spawns);
  }

  // FIXME: There are a number of places where invariant of a full expression
  // is not well-maitained. We clear spawn calls explicitly here.
  CilkSpawnCalls.clear();

  return IsValid;
}

namespace {

class CaptureBuilder : public RecursiveASTVisitor<CaptureBuilder> {
  Sema &S;

public:
  CaptureBuilder(Sema &S) : S(S) {}

  bool VisitDeclRefExpr(DeclRefExpr *E) {
    S.MarkDeclRefReferenced(E);
    return true;
  }

  bool TraverseLambdaExpr(LambdaExpr *E) {
    LambdaExpr::capture_init_iterator CI = E->capture_init_begin();

    for (LambdaExpr::capture_iterator C = E->capture_begin(),
           CEnd = E->capture_end();
         C != CEnd; ++C, ++CI) {
      if (C->capturesVariable())
        S.MarkVariableReferenced((*CI)->getLocStart(), C->getCapturedVar());
      else {
        assert(C->capturesThis() && "Capturing this expected");
        assert(isa<CXXThisExpr>(*CI) && "CXXThisExpr expected");
        S.CheckCXXThisCapture((*CI)->getLocStart(), /*explicit*/ false);
      }
    }
    assert(CI == E->capture_init_end() && "out of sync");
    // Only traverse the captures, and skip the body.
    return true;
  }

  /// Skip captured statements
  bool TraverseCapturedStmt(CapturedStmt *) { return true; }

  bool VisitCXXThisExpr(CXXThisExpr *E) {
    S.CheckCXXThisCapture(E->getLocStart(), /*explicit*/ false);
    return true;
  }
};

void CaptureVariablesInStmt(Sema &SemaRef, Stmt *S) {
  CaptureBuilder Builder(SemaRef);
  Builder.TraverseStmt(S);
}

void MarkFunctionAsSpawning(Sema &S) {
  DeclContext *DC = S.CurContext;
  if (!DC) {
    DC = S.CurContext;
    while (!DC->isFunctionOrMethod())
      DC = DC->getParent();
  }

  Decl::Kind Kind = DC->getDeclKind();
  if (Kind >= Decl::firstFunction && Kind <= Decl::lastFunction)
    FunctionDecl::castFromDeclContext(DC)->setSpawning();
  else if (Decl::Captured == Kind)
    CapturedDecl::castFromDeclContext(DC)->setSpawning();
  else {
    S.Diag(SourceLocation(), diag::err_spawn_invalid_decl)
      << DC->getDeclKindName();
  }
}

} // namespace

ExprResult Sema::BuildCilkSpawnExpr(Expr *E) {
  if (!E)
    return ExprError();

  if (ExprWithCleanups *EWC = dyn_cast<ExprWithCleanups>(E))
    E = EWC->getSubExpr();

  if (CilkSpawnExpr *CSE = dyn_cast<CilkSpawnExpr>(E)) {
    E = CSE->getSpawnExpr();
    assert(E && "Expr expected");
  }

  Stmt *Body = nullptr;
  {
    // Capture variables used in this full expression.
    ActOnCapturedRegionStart(E->getLocStart(), /*Scope*/ 0, CR_CilkSpawn,
                             /*NumParams*/ 1);
    CaptureVariablesInStmt(*this, E);
    Body = ActOnCapturedRegionEnd(E).get();
  }

  DeclContext *DC = CurContext;
  while (!(DC->isFunctionOrMethod() || DC->isRecord() || DC->isFileContext()))
    DC = DC->getParent();

  CapturedStmt *CS = cast<CapturedStmt>(Body);
  CilkSpawnDecl *Spawn = CilkSpawnDecl::Create(Context, DC, CS);
  DC->addDecl(Spawn);

  MarkFunctionAsSpawning(*this);
  return new (Context) CilkSpawnExpr(Spawn, E->getType());
}

static const Expr *
findMaterializedTemporary(const Expr *E, const MaterializeTemporaryExpr *&MTE) {
  // This might be a default initializer for a reference member. Walk over the
  // wrapper node for that.
  if (const CXXDefaultInitExpr *DAE = dyn_cast<CXXDefaultInitExpr>(E))
    E = DAE->getExpr();

  // Look through single-element init lists that claim to be lvalues. They're
  // just syntactic wrappers in this case.
  if (const InitListExpr *ILE = dyn_cast<InitListExpr>(E)) {
    if (ILE->getNumInits() == 1 && ILE->isGLValue()) {
      E = ILE->getInit(0);
      if (const CXXDefaultInitExpr *DAE = dyn_cast<CXXDefaultInitExpr>(E))
        E = DAE->getExpr();
    }
  }

  // Look through expressions for materialized temporaries (for now).
  if (const MaterializeTemporaryExpr *M =
      dyn_cast<MaterializeTemporaryExpr>(E)) {
    MTE = M;
    E = M->GetTemporaryExpr();
  }

  if (const CXXDefaultArgExpr *DAE = dyn_cast<CXXDefaultArgExpr>(E))
    E = DAE->getExpr();
  return E;
}

static QualType GetReceiverTmpType(const Expr *E) {
  do {
    if (const ExprWithCleanups *EWC = dyn_cast<ExprWithCleanups>(E))
      E = EWC->getSubExpr();
    const MaterializeTemporaryExpr *M = NULL;
    E = findMaterializedTemporary(E, M);
  } while (isa<ExprWithCleanups>(E));

  // Skip any implicit casts.
  SmallVector<const Expr *, 2> CommaLHSs;
  SmallVector<SubobjectAdjustment, 2> Adjustments;
  E = E->skipRValueSubobjectAdjustments(CommaLHSs, Adjustments);

  return E->getType();
}

static void addReceiverParams(Sema &SemaRef, CapturedDecl *CD,
                              QualType ReceiverType, QualType ReceiverTmpType) {
  if (!ReceiverType.isNull()) {
    DeclContext *DC = CapturedDecl::castToDeclContext(CD);
    assert(CD->getNumParams() >= 2);
    ImplicitParamDecl *Receiver =
      ImplicitParamDecl::Create(SemaRef.getASTContext(), DC, SourceLocation(),
                                /*IdInfo*/ 0, ReceiverType,
                                ImplicitParamDecl::Other);
    DC->addDecl(Receiver);
    CD->setParam(1, Receiver);
    if (!ReceiverTmpType.isNull()) {
      assert(CD->getNumParams() == 3);
      ImplicitParamDecl *ReceiverTmp = ImplicitParamDecl::Create(
          SemaRef.getASTContext(), DC, SourceLocation(), /*IdInfo*/ 0,
          ReceiverTmpType, ImplicitParamDecl::Other);
      DC->addDecl(ReceiverTmp);
      CD->setParam(2, ReceiverTmp);
    }
  }
}

CilkSpawnDecl *Sema::BuildCilkSpawnDecl(Decl *D) {
  VarDecl *VD = dyn_cast_or_null<VarDecl>(D);
  if (!VD || VD->isInvalidDecl())
    return nullptr;

  assert(VD->hasInit() && "initializer expected");

  if (VD->isStaticLocal()) {
    Diag(VD->getLocation(), diag::err_cannot_init_static_variable)
      << VD->getSourceRange();
    return nullptr;
  }

  // Pass the receiver (and possibly receiver temporary) to the
  // captured statement.
  unsigned NumParams = 2;

  // Receiver.
  QualType ReceiverType = Context.getCanonicalType(VD->getType());
  ReceiverType = Context.getPointerType(ReceiverType);

  // Receiver temporary.
  QualType ReceiverTmpType;
  if (VD->getType()->isReferenceType() && extendsLifetimeOfTemporary(VD)) {
    ReceiverTmpType = GetReceiverTmpType(VD->getInit());
    if (!ReceiverTmpType.isNull()) {
      NumParams = 3;
      ReceiverTmpType = Context.getPointerType(ReceiverTmpType);
    }
  }

  // Start building the Captured statement.
  ActOnCapturedRegionStart(D->getLocStart(), /*Scope*/ 0, CR_CilkSpawn,
                           NumParams);

  // Create a DeclStmt as the CapturedStatement body.
  DeclStmt *Body = new (Context)
    DeclStmt(DeclGroupRef(VD), VD->getLocStart(), VD->getLocEnd());
  CaptureVariablesInStmt(*this, Body);

  StmtResult R = ActOnCapturedRegionEnd(Body);

  DeclContext *DC = CurContext;
  while (!(DC->isFunctionOrMethod() || DC->isRecord() || DC->isFileContext()))
    DC = DC->getParent();

  CapturedStmt *CS = cast<CapturedStmt>(R.get());
  CilkSpawnDecl *Spawn = CilkSpawnDecl::Create(Context, DC, CS);
  DC->addDecl(Spawn);

  // Initialize receiver and its associated temporary parameters.
  addReceiverParams(*this, Spawn->getCapturedStmt()->getCapturedDecl(),
                    ReceiverType, ReceiverTmpType);

  MarkFunctionAsSpawning(*this);
  return Spawn;
}

namespace {
// Diagnose any _Cilk_spawn expressions (see comment below). InSpawn indicates
// that S is contained within a spawn, e.g. _Cilk_spawn foo(_Cilk_spawn bar())
class DiagnoseCilkSpawnHelper
  : public RecursiveASTVisitor<DiagnoseCilkSpawnHelper> {
  Sema &SemaRef;
  bool isStmtExpr;

public:
  explicit DiagnoseCilkSpawnHelper(Sema &S, bool isStmtExpr):
      SemaRef(S), isStmtExpr(isStmtExpr) {}

  bool TraverseCompoundStmt(CompoundStmt *) { return true; }
  bool VisitCallExpr(CallExpr *E) {
    if (E->isCilkSpawnCall()){
      if (isStmtExpr){
        SemaRef.Diag(E->getCilkSpawnLoc(),
                     SemaRef.PDiag(diag::err_cilk_spawn_disable));
      } else {
        SemaRef.Diag(E->getCilkSpawnLoc(),
                     SemaRef.PDiag(diag::err_spawn_not_whole_expr)
                     << E->getSourceRange());
      }
    }
    return true;
  }
  bool VisitCilkSpawnDecl(CilkSpawnDecl *D) {
    TraverseStmt(D->getSpawnStmt());
    return true;
  }
};

} // anonymous namespace

// Check that _Cilk_spawn is used only:
//  - as the entire body of an expression statement,
//  - as the entire right hand side of an assignment expression that is the
//    entire body of an expression statement, or
//  - as the entire initializer-clause in a simple declaration.
//
// Since this is run per-compound scope stmt, we don't traverse into sub-
// compound scopes, but we do need to traverse into loops, ifs, etc. in case of:
// if (cond) _Cilk_spawn foo();
//           ^~~~~~~~~~~~~~~~~ not a compound scope
void Sema::DiagnoseCilkSpawn(Stmt *S, bool isStmtExpr) {
  DiagnoseCilkSpawnHelper D(*this, isStmtExpr);

  if (isStmtExpr){
    D.TraverseStmt (S);
    return;
  }
  // already checked.
  if (isa<Expr>(S))
    return;

  switch (S->getStmtClass()) {
  case Stmt::AttributedStmtClass:
    DiagnoseCilkSpawn(cast<AttributedStmt>(S)->getSubStmt());
    break;
  case Stmt::CompoundStmtClass:
  case Stmt::DeclStmtClass:
    return; // already checked
  case Stmt::CapturedStmtClass:
    DiagnoseCilkSpawn(cast<CapturedStmt>(S)->getCapturedStmt());
    break;
  case Stmt::CilkForStmtClass: {
    CilkForStmt *CF = cast<CilkForStmt>(S);
    if (CF->getInit())
      D.TraverseStmt(CF->getInit());
    if (CF->getCond())
      D.TraverseStmt(CF->getCond());
    if (CF->getInc())
      D.TraverseStmt(CF->getInc());
    // the cilk for body is already checked.
    break;
  }
  case Stmt::CXXCatchStmtClass:
    DiagnoseCilkSpawn(cast<CXXCatchStmt>(S)->getHandlerBlock());
    break;
  case Stmt::CXXForRangeStmtClass: {
    CXXForRangeStmt *FR = cast<CXXForRangeStmt>(S);
    D.TraverseStmt(FR->getRangeInit());
    DiagnoseCilkSpawn(FR->getBody());
    break;
  }
  case Stmt::CXXTryStmtClass:
    DiagnoseCilkSpawn(cast<CXXTryStmt>(S)->getTryBlock());
    break;
  case Stmt::DoStmtClass: {
    DoStmt *DS = cast<DoStmt>(S);
    D.TraverseStmt(DS->getCond());
    DiagnoseCilkSpawn(DS->getBody());
    break;
  }
  case Stmt::ForStmtClass: {
    ForStmt *F = cast<ForStmt>(S);
    if (F->getInit())
      D.TraverseStmt(F->getInit());
    if (F->getCond())
      D.TraverseStmt(F->getCond());
    if (F->getInc())
      D.TraverseStmt(F->getInc());
    DiagnoseCilkSpawn(F->getBody());
    break;
  }
  case Stmt::IfStmtClass: {
    IfStmt *I = cast<IfStmt>(S);
    D.TraverseStmt(I->getCond());
    DiagnoseCilkSpawn(I->getThen());
    if (I->getElse())
      DiagnoseCilkSpawn(I->getElse());
    break;
  }
  case Stmt::LabelStmtClass:
    DiagnoseCilkSpawn(cast<LabelStmt>(S)->getSubStmt());
    break;
  case Stmt::SwitchStmtClass: {
    SwitchStmt *SS = cast<SwitchStmt>(S);
    if (const DeclStmt *DS = SS->getConditionVariableDeclStmt())
      D.TraverseStmt(const_cast<DeclStmt *>(DS));
    D.TraverseStmt(SS->getCond());
    DiagnoseCilkSpawn(SS->getBody());
    break;
  }
  case Stmt::CaseStmtClass:
  case Stmt::DefaultStmtClass:
    DiagnoseCilkSpawn(cast<SwitchCase>(S)->getSubStmt());
    break;
  case Stmt::WhileStmtClass: {
    WhileStmt *W = cast<WhileStmt>(S);
    D.TraverseStmt(W->getCond());
    DiagnoseCilkSpawn(W->getBody());
    break;
  }
  default:
    D.TraverseStmt(S);
    break;
  }
}

StmtResult Sema::BuildCilkForStmt(SourceLocation CilkForLoc,
                                  SourceLocation LParenLoc,
                                  Stmt *Init, Expr *Cond, Expr *Inc,
                                  SourceLocation RParenLoc, Stmt *Body,
                                  Expr *LoopCount, Expr *Stride,
                                  QualType SpanType) {
  CilkForScopeInfo *FSI = getCurCilkFor();
  assert(FSI && "CilkForScopeInfo is out of sync");
  CapturedDecl *CD = FSI->TheCapturedDecl;
  RecordDecl *RD = FSI->TheRecordDecl;
  DeclContext *DC = CapturedDecl::castToDeclContext(CD);
  bool IsDependent = DC->isDependentContext();

  // Handle the special case that the Cilk for body is not a compound statement
  // and it has a Cilk spawn. In this case, the implicit compound scope should
  // have this information.
  if (getCurCompoundScope().HasCilkSpawn && !isa<CompoundStmt>(Body))
    DiagnoseCilkSpawn(Body);

  SmallVector<CapturedStmt::Capture, 4> Captures;
  SmallVector<Expr *, 4> CaptureInits;
  BuildCapturedStmtCaptureList(Captures, CaptureInits, FSI->Captures);

  CapturedStmt *CapturedBody = CapturedStmt::Create(
      getASTContext(), Body, static_cast<CapturedRegionKind>(FSI->CapRegionKind),
      Captures, CaptureInits, CD, RD);

  CD->setBody(CapturedBody->getCapturedStmt());
  RD->completeDefinition();

  ExprResult AdjustExpr;
  // Set parameters for the outlined function.
  // Build the initial value for the inner loop control variable.
  if (!IsDependent) {
    assert(LoopCount && "invalid null loop count expression");
    QualType Ty = LoopCount->getType().getNonReferenceType();

    // In the following, the source location of the loop control variable
    // will be used for diagnostics.
    SourceLocation VarLoc = FSI->LoopControlVar->getLocation();
    assert(VarLoc.isValid() && "invalid source location");
    assert(CD->getNumParams() == 3 && "bad signature");

    ImplicitParamDecl *Low
      = ImplicitParamDecl::Create(Context, DC, VarLoc,
                                  &Context.Idents.get("__low"), Ty,
                                  ImplicitParamDecl::Other);
    DC->addDecl(Low);
    CD->setParam(1, Low);

    ImplicitParamDecl *High
      = ImplicitParamDecl::Create(Context, DC, VarLoc,
                                  &Context.Idents.get("__high"), Ty,
                                  ImplicitParamDecl::Other);
    DC->addDecl(High);
    CD->setParam(2, High);

    // Build a full expression "inner_loop_var += stride * low"
    {
      EnterExpressionEvaluationContext EvalScope(
          *this, ExpressionEvaluationContext::PotentiallyEvaluated);
      // Both low and stride experssions are of type integral.
      ExprResult LowExpr = BuildDeclRefExpr(Low, Ty, VK_LValue, VarLoc);
      assert(!LowExpr.isInvalid() && "invalid expr");

      assert(Stride && "invalid null stride expression");
      // Need to keep the orginal stride unmodified, since it has been part
      // of the LoopCount expression. If Stride is already an implicit cast
      // expression, then BuildBinOp may replace this cast into another type.
      // E.g.
      //
      // short s = 2;
      // _Cilk_for (int *p = a; p != b; p += s);
      //
      // During the loop count calculation, Stride is an implicit cast
      // expression of type int. Since LowExpr has type unsigned long,
      // BuildBinOp will try cast Stride into unsigned long, by replacing
      // the int implicit cast into unsigned long implicit cast, this
      // invalidates the loop count expression built.
      //
      // The solution is to get the raw Stride expression from the source
      // and create a new implicit cast expression of desired type,
      // if necessary.
      //
      Stride = Stride->IgnoreImpCastsAsWritten();

      ExprResult StepExpr =
        BuildBinOp(CurScope, VarLoc, BO_Mul, LowExpr.get(), Stride);
      assert(!StepExpr.isInvalid() && "invalid expression");
      Expr *Step = StepExpr.get();
      Step = ImplicitCastExpr::Create(Context, SpanType, CK_IntegralCast, Step,
                                      0, VK_LValue);
      Step = DefaultLvalueConversion(Step).get();

      VarDecl *InnerVar = FSI->InnerLoopControlVar;
      ExprResult InnerVarExpr
        = BuildDeclRefExpr(InnerVar, InnerVar->getType(), VK_LValue, VarLoc);
      assert(!InnerVarExpr.isInvalid() && "invalid expression");

      // The '+=' operation could fail if the loop control variable is of
      // class type and this may introduce cleanups.
      AdjustExpr = BuildBinOp(CurScope, VarLoc, BO_AddAssign,
                              InnerVarExpr.get(), Step);
      if (!AdjustExpr.isInvalid()) {
        if (Step->hasNonTrivialCall(Context))
          Cleanup.setExprNeedsCleanups(true);

        AdjustExpr = MaybeCreateExprWithCleanups(AdjustExpr);
      }
      // FIXME: Should mark the CilkForDecl as invalid?
      // FIXME: Should install the adjustment expression into the CilkForStmt?
    }
  }

  CilkForStmt *Result = new (Context)
    CilkForStmt(Init, Cond, Inc, CapturedBody, LoopCount,
                CilkForLoc, LParenLoc, RParenLoc);

  // TODO: move into constructor?
  Result->setLoopControlVar(FSI->LoopControlVar);
  Result->setInnerLoopControlVar(FSI->InnerLoopControlVar);
  Result->setInnerLoopVarAdjust(AdjustExpr.get());

  if (FSI->ExprNeedsCleanups)
    Cleanup.setExprNeedsCleanups(true);

  DiscardCleanupsInEvaluationContext();
  PopExpressionEvaluationContext();
  PopDeclContext();
  // Pop the compound scope we inserted implicitly.
  PopCompoundScope();
  PopFunctionScopeInfo();

  return Result;
}

ExprResult
Sema::ActOnCilkSpawnCall(SourceLocation SpawnLoc, Expr *E) {
  assert(FunctionScopes.size() > 0 && "FunctionScopes missing TU scope");
  if (FunctionScopes.size() < 1 ||
      getCurFunction()->CompoundScopes.size() < 1) {
    Diag(SpawnLoc, diag::err_spawn_invalid_scope);
    return ExprError();
  }

  return BuildCilkSpawnCall(SpawnLoc, E);
}

ExprResult
Sema::BuildCilkSpawnCall(SourceLocation SpawnLoc, Expr *E) {
  assert(E && "null expression");

  CallExpr *Call = dyn_cast<CallExpr>(E->IgnoreImplicitForCilkSpawn());

  if (Call) {
    if (CXXOperatorCallExpr *O = dyn_cast<CXXOperatorCallExpr>(Call))
      Call = O->getOperator() == OO_Call ? Call : 0;
    else if (dyn_cast<CXXPseudoDestructorExpr>(Call->getCallee()))
      return E; // simply discard the spawning of pseudo destructor
  }

  if (!Call) {
    Diag(E->getExprLoc(), PDiag(diag::err_not_a_call) << getExprRange(E));
    return ExprError();
  }

  if (Call->isCilkSpawnCall()) {
    Diag(E->getExprLoc(), diag::err_spawn_spawn);
    return ExprError();
  }

  Call->setCilkSpawnLoc(SpawnLoc);
  getCurCompoundScope().setHasCilkSpawn();
  CilkSpawnCalls.push_back(Call);

  return E;
}

Decl *TemplateDeclInstantiator::VisitCilkSpawnDecl(CilkSpawnDecl *D) {
  VarDecl *VD = D->getReceiverDecl();
  assert(VD && "Cilk spawn receiver expected");
  Decl *NewDecl = SemaRef.SubstDecl(VD, Owner, TemplateArgs);
  return SemaRef.BuildCilkSpawnDecl(NewDecl);
}

CilkForScopeInfo::~CilkForScopeInfo() { }

// static bool isValidCilkContext(Sema &S, SourceLocation Loc, StringRef Keyword) {
//   // Cilk is not permitted in unevaluated contexts.
//   if (S.isUnevaluatedContext()) {
//     S.Diag(Loc, diag::err_cilk_unevaluated_context) << Keyword;
//     return false;
//   }

//   // Any other usage must be within a function.
//   FunctionDecl *FD = dyn_cast<FunctionDecl>(S.CurContext);
//   if (!FD) {
//     S.Diag(Loc, diag::err_cilk_outside_function) << Keyword;
//     return false;
//   }

//   // TODO: Add more checks for the validity of the current context for Cilk.
//   // (See isValidCoroutineContext for example code.)
//   return true;
// }

// /// Check that this is a context in which a Cilk keywords can appear.
// static FunctionScopeInfo *checkCilkContext(Sema &S, SourceLocation Loc,
//                                            StringRef Keyword) {
//   if (!isValidCilkContext(S, Loc, Keyword))
//     return nullptr;

//   assert(isa<FunctionDecl>(S.CurContext) && "not in a function scope");
//   // FunctionDecl *FD = cast<FunctionDecl>(S.CurContext);
//   FunctionScopeInfo *ScopeInfo = S.getCurFunction();
//   assert(ScopeInfo && "missing function scope for function");

//   return ScopeInfo;
// }

// StmtResult
// Sema::ActOnCilkSpawnStmt(SourceLocation SpawnLoc, Stmt *SubStmt) {
//   if (!checkCilkContext(*this, SpawnLoc, "_Cilk_spawn"))
//     return StmtError();

//   DiagnoseUnusedExprResult(SubStmt);

//   PushFunctionScope();
//   // TODO: Figure out how to prevent jumps into and out of the spawned
//   // substatement.
//   getCurFunction()->setHasBranchProtectedScope();
//   PushExpressionEvaluationContext(
//       ExpressionEvaluationContext::PotentiallyEvaluated);

//   StmtResult Result = new (Context) CilkSpawnStmt(SpawnLoc, SubStmt);

//   PopExpressionEvaluationContext();
//   PopFunctionScopeInfo();

//   return Result;
// }

// StmtResult
// Sema::ActOnCilkSyncStmt(SourceLocation SyncLoc) {
//   if (!checkCilkContext(*this, SyncLoc, "_Cilk_sync"))
//     return StmtError();
//   return new (Context) CilkSyncStmt(SyncLoc);
// }

// ExprResult Sema::ActOnCilkSpawnExpr(SourceLocation Loc, Expr *E) {
//   FunctionScopeInfo *CilkCtx = checkCilkContext(*this, Loc, "_Cilk_spawn");
//   if (!CilkCtx) {
//     CorrectDelayedTyposInExpr(E);
//     return ExprError();
//   }
//   if (E->getType()->isPlaceholderType()) {
//     ExprResult R = CheckPlaceholderExpr(E);
//     if (R.isInvalid()) return ExprError();
//     E = R.get();
//   }

//   return BuildCilkSpawnExpr(Loc, E);
// }

// ExprResult Sema::BuildCilkSpawnExpr(SourceLocation Loc, Expr *E) {
//   FunctionScopeInfo *CilkCtx = checkCilkContext(*this, Loc, "_Cilk_spawn");
//   if (!CilkCtx)
//     return ExprError();

//   if (E->getType()->isPlaceholderType()) {
//     ExprResult R = CheckPlaceholderExpr(E);
//     if (R.isInvalid()) return ExprError();
//     E = R.get();
//   }

//   return new (Context) CilkSpawnExpr(Loc, E);
// }
