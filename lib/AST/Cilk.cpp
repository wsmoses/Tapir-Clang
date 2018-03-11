//===--- Cilk.cpp - Cilk AST Node Implementation --------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the subclasses for Cilk.
//
//===----------------------------------------------------------------------===//

#include "clang/AST/Cilk.h"
#include "clang/AST/Decl.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTLambda.h"
#include "clang/AST/ASTMutationListener.h"
#include "clang/AST/Attr.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclObjC.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/PrettyPrinter.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/TypeLoc.h"
#include "clang/Basic/Builtins.h"
#include "clang/Basic/IdentifierTable.h"
#include "clang/Basic/Module.h"
#include "clang/Basic/Specifiers.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/Frontend/FrontendDiagnostic.h"
#include "llvm/Support/ErrorHandling.h"
#include <algorithm>

using namespace clang;

CilkSpawnDecl::CilkSpawnDecl(DeclContext *DC, CapturedStmt *Spawn) :
    Decl(CilkSpawn, DC, Spawn->getLocStart()), CapturedSpawn(Spawn) {
}

CilkSpawnDecl *CilkSpawnDecl::Create(ASTContext &C, DeclContext *DC,
                                     CapturedStmt *Spawn) {
  return new (C, DC) CilkSpawnDecl(DC, Spawn);
}

CilkSpawnDecl *CilkSpawnDecl::CreateDeserialized(ASTContext &C, unsigned ID) {
  return new (C, ID) CilkSpawnDecl(nullptr, nullptr);
}

Stmt *CilkSpawnDecl::getSpawnStmt() {
  return getCapturedStmt()->getCapturedStmt();
}

bool CilkSpawnDecl::hasReceiver() const {
  const Stmt *S = getSpawnStmt();
  assert(S && "null spawn statement");
  return isa<DeclStmt>(S);
}

VarDecl *CilkSpawnDecl::getReceiverDecl() const {
  Stmt *S = const_cast<Stmt *>(getSpawnStmt());
  assert(S && "null spawn statement");
  if (DeclStmt *DS = dyn_cast<DeclStmt>(S)) {
    assert(DS->isSingleDecl() && "single declaration expected");
    return cast<VarDecl>(DS->getSingleDecl());
  }

  return 0;
}

bool Decl::isSpawning() const {
  if (const FunctionDecl *FD = dyn_cast<FunctionDecl>(this))
    return FD->isSpawning();
  else if (const CapturedDecl *CD = dyn_cast<CapturedDecl>(this))
    return CD->isSpawning();

  return false;
}

SourceLocation CilkSpawnExpr::getLocStart() const {
  return TheSpawn->getSpawnStmt()->getLocStart();
}

SourceLocation CilkSpawnExpr::getLocEnd() const {
  return TheSpawn->getSpawnStmt()->getLocEnd();
}

Expr *Expr::IgnoreImpCastsAsWritten() {
  Expr *E = this;
  while (ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(E))
    E = ICE->getSubExprAsWritten();
  return E;
}

Expr *Expr::getSubExprAsWritten() {
  Expr *E = this;
  while (true) {
    if (ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(E))
      E = ICE->getSubExprAsWritten();
    else if (MaterializeTemporaryExpr *MTE
             = dyn_cast<MaterializeTemporaryExpr>(E))
      E = MTE->GetTemporaryExpr();
    else if (CXXBindTemporaryExpr *BTE = dyn_cast<CXXBindTemporaryExpr>(E))
      E = BTE->getSubExpr();
    else if (ExprWithCleanups *EWC = dyn_cast<ExprWithCleanups>(E))
      E = EWC->getSubExpr();
    else
      break;
  }

  return E;
}

Expr *Expr::IgnoreImplicitForCilkSpawn() {
  Expr *E = this;
  while (E) {
    E = E->IgnoreParens();
    if (ImplicitCastExpr *CE = dyn_cast<ImplicitCastExpr>(E))
      E = CE->getSubExprAsWritten();
    else if (ExprWithCleanups *EWC = dyn_cast<ExprWithCleanups>(E))
      E = EWC->getSubExpr();
    else if (MaterializeTemporaryExpr *MTE
             = dyn_cast<MaterializeTemporaryExpr>(E))
      E = MTE->GetTemporaryExpr();
    else if (CXXBindTemporaryExpr *BTE = dyn_cast<CXXBindTemporaryExpr>(E))
      E = BTE->getSubExpr();
    else if (CXXConstructExpr *CE = dyn_cast<CXXConstructExpr>(E)) {
      // CXXTempoaryObjectExpr represents a functional cast with != 1 arguments
      // so handle it the same way as CXXFunctionalCastExpr
      if (isa<CXXTemporaryObjectExpr>(CE))
        break;
      if (CE->getNumArgs() >= 1)
        E = CE->getArg(0);
      else
        break;
    } else
      break;
  }

  return E->IgnoreParens();
}

bool Expr::isCilkSpawn() const {
  const Expr *E = IgnoreImplicitForCilkSpawn();
  if (const CallExpr *CE = dyn_cast_or_null<CallExpr>(E))
    return CE->isCilkSpawnCall();

  return false;
}

// CilkForGrainsizeStmt::CilkForGrainsizeStmt(Expr *Grainsize, Stmt *CilkFor,
//                                            SourceLocation LocStart)
//     : Stmt(CilkForGrainsizeStmtClass), LocStart(LocStart) {
//   SubExprs[GRAINSIZE] = Grainsize;
//   SubExprs[CILK_FOR] = CilkFor;
// }

// CilkForGrainsizeStmt::CilkForGrainsizeStmt(EmptyShell Empty)
//     : Stmt(CilkForGrainsizeStmtClass), LocStart() {
//   SubExprs[GRAINSIZE] = 0;
//   SubExprs[CILK_FOR] = 0;
// }

/// \brief Construct an empty Cilk for statement.
CilkForStmt::CilkForStmt(EmptyShell Empty)
    : Stmt(CilkForStmtClass, Empty), LoopControlVar(0), InnerLoopControlVar(0),
      InnerLoopVarAdjust(0) {
  SubExprs[INIT] = 0;
  SubExprs[COND] = 0;
  SubExprs[INC] = 0;
  SubExprs[BODY] = 0;
  SubExprs[LOOP_COUNT] = 0;
}

/// \brief Construct a Cilk for statement.
CilkForStmt::CilkForStmt(Stmt *Init, Expr *Cond, Expr *Inc, CapturedStmt *Body,
                         Expr *LoopCount, SourceLocation FL, SourceLocation LP,
                         SourceLocation RP)
    : Stmt(CilkForStmtClass), CilkForLoc(FL), LParenLoc(LP), RParenLoc(RP),
      LoopControlVar(0), InnerLoopControlVar(0), InnerLoopVarAdjust(0) {
  assert(Init && Cond && Inc && Body && "null argument unexpected");

  SubExprs[INIT] = Init;
  SubExprs[COND] = Cond;
  SubExprs[INC] = Inc;
  SubExprs[BODY] = Body;
  SubExprs[LOOP_COUNT] = LoopCount;
}
