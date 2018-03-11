//===--- Cilk.h - Types for Cilk Plus ------ --------------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#ifndef LLVM_CLANG_AST_CILK_H
#define LLVM_CLANG_AST_CILK_H

#include "clang/AST/Decl.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"

namespace clang {
  
/// CilkSyncStmt - This represents a _Cilk_sync
class CilkSyncStmt : public Stmt {
  SourceLocation SyncLoc;

 public:
  explicit CilkSyncStmt(SourceLocation SL)
    : Stmt(CilkSyncStmtClass), SyncLoc(SL) {}
  explicit CilkSyncStmt(EmptyShell E) : Stmt(CilkSyncStmtClass, E) {}

  void setSyncLoc(SourceLocation L) { SyncLoc = L; }
  SourceLocation getSyncLoc() const { return SyncLoc; }

  SourceLocation getLocStart() const LLVM_READONLY { return SyncLoc; }
  SourceLocation getLocEnd() const LLVM_READONLY { return SyncLoc; }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == CilkSyncStmtClass;
  }
  child_range children() {
    return child_range(child_iterator(), child_iterator());
  }
};

// /// \brief This represents a Cilk for grainsize statement.
// /// \code
// /// #pragma cilk grainsize = expr
// /// _Cilk_for(...) { ... }
// /// \endcode
// class CilkForGrainsizeStmt : public Stmt {
//  private:
//   enum { GRAINSIZE, CILK_FOR, LAST };
//   Stmt *SubExprs[LAST];
//   SourceLocation LocStart;

//  public:
//   /// \brief Construct a Cilk for grainsize statement.
//   CilkForGrainsizeStmt(Expr *Grainsize, Stmt *CilkFor, SourceLocation LocStart);

//   /// \brief Construct an empty Cilk for grainsize statement.
//   explicit CilkForGrainsizeStmt(EmptyShell Empty);

//   SourceLocation getLocStart() const LLVM_READONLY { return LocStart; }
//   SourceLocation getLocEnd() const LLVM_READONLY {
//     return SubExprs[CILK_FOR]->getLocEnd();
//   }

//   Expr *getGrainsize() { return reinterpret_cast<Expr *>(SubExprs[GRAINSIZE]); }
//   const Expr *getGrainsize() const {
//     return const_cast<CilkForGrainsizeStmt *>(this)->getGrainsize();
//   }

//   Stmt *getCilkFor() { return SubExprs[CILK_FOR]; }
//   const Stmt *getCilkFor() const { return SubExprs[CILK_FOR]; }

//   static bool classof(const Stmt *T) {
//     return T->getStmtClass() == CilkForGrainsizeStmtClass;
//   }

//   child_range children() { return child_range(SubExprs, SubExprs + LAST); }
// };

/// \brief This represents a Cilk for statement.
/// \code
/// _Cilk_for (int i = 0; i < n; ++i) {
///   // ...
/// }
/// \endcode
class CilkForStmt : public Stmt {
 private:
  /// \brief An enumeration for accessing stored statements in a Cilk for
  /// statement.
  enum { INIT, COND, INC, BODY, LOOP_COUNT, LAST };

  Stmt *SubExprs[LAST]; // SubExprs[INIT] is an expression or declstmt.
  // SubExprs[BODY] is a CapturedStmt.

  /// \brief The source location of '_Cilk_for'.
  SourceLocation CilkForLoc;

  /// \brief The source location of opening parenthesis.
  SourceLocation LParenLoc;

  /// \brief The source location of closing parenthesis.
  SourceLocation RParenLoc;

  /// \brief The loop control variable.
  const VarDecl *LoopControlVar;

  /// \brief The local copy of the loop control variable.
  VarDecl *InnerLoopControlVar;

  /// \brief The implicit generated full expression for adjusting
  /// the inner loop control variable.
  Expr *InnerLoopVarAdjust;

 public:
  /// \brief Construct a Cilk for statement.
  CilkForStmt(Stmt *Init, Expr *Cond, Expr *Inc, CapturedStmt *Body,
              Expr *LoopCount, SourceLocation FL, SourceLocation LP,
              SourceLocation RP);

  /// \brief Construct an empty Cilk for statement.
  explicit CilkForStmt(EmptyShell Empty);

  /// \brief Retrieve the initialization expression or declaration statement.
  Stmt *getInit() { return SubExprs[INIT]; }
  const Stmt *getInit() const { return SubExprs[INIT]; }

  /// \brief Retrieve the loop condition expression.
  Expr *getCond() { return reinterpret_cast<Expr *>(SubExprs[COND]); }
  const Expr *getCond() const {
    return reinterpret_cast<Expr *>(SubExprs[COND]);
  }

  /// \brief Retrieve the loop increment expression.
  Expr *getInc() { return reinterpret_cast<Expr *>(SubExprs[INC]); }
  const Expr *getInc() const { return reinterpret_cast<Expr *>(SubExprs[INC]); }

  /// \brief Retrieve the loop body.
  CapturedStmt *getBody() {
    return reinterpret_cast<CapturedStmt *>(SubExprs[BODY]);
  }
  const CapturedStmt *getBody() const {
    return reinterpret_cast<CapturedStmt *>(SubExprs[BODY]);
  }

  /// \brief Retrieve the loop count expression.
  Expr *getLoopCount() {
    return reinterpret_cast<Expr *>(SubExprs[LOOP_COUNT]);
  }
  const Expr *getLoopCount() const {
    return reinterpret_cast<Expr *>(SubExprs[LOOP_COUNT]);
  }

  const VarDecl *getLoopControlVar() const { return LoopControlVar; }
  void setLoopControlVar(const VarDecl *V) { LoopControlVar = V; }

  VarDecl *getInnerLoopControlVar() const { return InnerLoopControlVar; }
  void setInnerLoopControlVar(VarDecl *V) { InnerLoopControlVar = V; }

  Expr *getInnerLoopVarAdjust() const { return InnerLoopVarAdjust; }
  void setInnerLoopVarAdjust(Expr *E) { InnerLoopVarAdjust = E; }

  SourceLocation getCilkForLoc() const LLVM_READONLY { return CilkForLoc; }
  SourceLocation getLParenLoc() const LLVM_READONLY { return LParenLoc; }
  SourceLocation getRParenLoc() const LLVM_READONLY { return RParenLoc; }

  void setCilkForLoc(SourceLocation L) { CilkForLoc = L; }
  void setLParenLoc(SourceLocation L) { LParenLoc = L; }
  void setRParenLoc(SourceLocation L) { RParenLoc = L; }

  SourceLocation getLocStart() const LLVM_READONLY { return CilkForLoc; }
  SourceLocation getLocEnd() const LLVM_READONLY {
    return SubExprs[BODY]->getLocEnd();
  }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == CilkForStmtClass;
  }

  child_range children() {
    return child_range(&SubExprs[0], &SubExprs[0] + LAST);
  }
};

class CilkSpawnDecl : public Decl {
  /// \brief The CapturedStmt associated to the expression or statement with
  /// a Cilk spawn call.
  CapturedStmt *CapturedSpawn;

  CilkSpawnDecl(DeclContext *DC, CapturedStmt *Spawn);

 public:
  static CilkSpawnDecl *Create(ASTContext &C, DeclContext *DC,
                               CapturedStmt *Spawn);
  static CilkSpawnDecl *CreateDeserialized(ASTContext &C, unsigned ID);

  /// \brief Returns if this Cilk spawn has a receiver.
  bool hasReceiver() const;

  /// \brief Returns the receiver declaration.
  VarDecl *getReceiverDecl() const;

  /// \brief Returns the expression or statement with a Cilk spawn.
  Stmt *getSpawnStmt();
  const Stmt *getSpawnStmt() const {
    return const_cast<CilkSpawnDecl *>(this)->getSpawnStmt();
  }

  /// \brief Returns the associated CapturedStmt.
  CapturedStmt *getCapturedStmt() { return CapturedSpawn; }
  const CapturedStmt *getCapturedStmt() const { return CapturedSpawn; }

  static bool classof(const Decl *D) { return classofKind(D->getKind()); }
  static bool classofKind(Kind K) { return K == CilkSpawn; }

  friend class ASTDeclReader;
  friend class ASTDeclWriter;
};

/// \brief Adaptor class for mixing a CilkSpawnDecl with expressions.
class CilkSpawnExpr : public Expr {
  CilkSpawnDecl *TheSpawn;

public:
  explicit CilkSpawnExpr(CilkSpawnDecl *D, QualType Ty)
      : Expr(CilkSpawnExprClass, Ty, VK_RValue, OK_Ordinary,
             Ty->isDependentType(), Ty->isDependentType(),
             Ty->isInstantiationDependentType(), false), TheSpawn(D) { }
  
  /// \brief Build an empty block expression.
  explicit CilkSpawnExpr(EmptyShell Empty) : Expr(CilkSpawnExprClass, Empty) { }

  const CilkSpawnDecl *getSpawnDecl() const { return TheSpawn; }
  CilkSpawnDecl *getSpawnDecl() { return TheSpawn; }
  void setSpawnDecl(CilkSpawnDecl *D) { TheSpawn = D; }

  Stmt *getSpawnStmt() { return TheSpawn->getSpawnStmt(); }
  const Stmt *getSpawnStmt() const { return TheSpawn->getSpawnStmt(); }

  Expr *getSpawnExpr() { return dyn_cast<Expr>(getSpawnStmt()); }
  const Expr *getSpawnExpr() const { return dyn_cast<Expr>(getSpawnStmt()); }

  SourceLocation getLocStart() const LLVM_READONLY;
  SourceLocation getLocEnd() const LLVM_READONLY;

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == CilkSpawnExprClass;
  }

  child_range children() {
    return child_range(child_iterator(), child_iterator());
  }
};
}  // end namespace clang

#endif
