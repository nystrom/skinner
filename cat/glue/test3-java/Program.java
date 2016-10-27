class Program {
  Expression body;
  Program(Expression body) { this.body = body; }

  public String toString() {
    return "Program(" + body + ")";
  }
}

interface Expression { }

class BooleanLit implements Expression {
  boolean value;

  BooleanLit(boolean value) {
    this.value = value;
  }

  public String toString() {
    return "BooleanLit(" + value + ")";
  }
}

class IntLit implements Expression {
  int value;

  IntLit(int value) {
    this.value = value;
  }

  public String toString() {
    return "IntLit(" + value + ")";
  }
}

class Var implements Expression {
  String name;

  Var(String name) {
    this.name = name;
  }

  public String toString() {
    return "Var(" + name + ")";
  }
}

class If implements Expression {
  Expression cond;
  Expression then;
  Expression elsx;

  If(Expression cond, Expression then, Expression elsx) {
    this.cond = cond;
    this.then = then;
    this.elsx = elsx;
  }

  public String toString() {
    return "If(" + cond + ", " + then + ", " + elsx + ")";
  }
}

class Assign implements Expression {
  String lhs;
  Expression rhs;

  Assign(String lhs, Expression rhs) {
    this.lhs = lhs;
    this.rhs = rhs;
  }

  public String toString() {
    return "Assign(" + lhs + ", " + rhs + ")";
  }
}

class Seq implements Expression {
  Expression fst;
  Expression snd;

  Seq(Expression fst, Expression snd) {
    this.fst = fst;
    this.snd = snd;
  }

  public String toString() {
    return "Seq(" + fst + ", " + snd + ")";
  }
}

class Skip implements Expression {
  Skip() { }

  public String toString() {
    return "Skip";
  }
}

class While implements Expression {
  Expression cond;
  Expression body;

  While(Expression cond, Expression body) {
    this.cond = cond;
    this.body = body;
  }

  public String toString() {
    return "While(" + cond + ", " + body + ")";
  }
}

class BinExp implements Expression {
  BinaryOp op;
  Expression left;
  Expression right;

  BinExp(BinaryOp op, Expression left, Expression right) {
    this.op = op;
    this.left = left;
    this.right = right;
  }

  public String toString() {
    return "BinExp(" + op + ", " + left + ", " + right + ")";
  }
}

enum BinaryOp { Plus, Minus, Times, Divide, Remainder, Less, Greater, Equals, LessEq, GreaterEq, NotEq }


