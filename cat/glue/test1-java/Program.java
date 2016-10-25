class Program {
  Declaration[] decls;
  Program(Declaration[] decls) { this.decls = decls; }

  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("Program [");
    String sep = "";
    for (Declaration d : decls) {
      sb.append(sep);
      sep = ", ";
      sb.append(d);
    }
    sb.append("]");
    return sb.toString();
  }
}

interface Declaration { }

class Method implements Declaration {
  String id;
  String[] params;
  Expression body;

  Method(String id, String[] params, Expression body) {
    this.id = id;
    this.params = params;
    this.body = body;
  }

  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("Method(");
    sb.append(id);
    sb.append(", [");
    String sep = "";
    for (String d : params) {
      sb.append(sep);
      sep = ", ";
      sb.append(d);
    }
    sb.append("], ");
    sb.append(body);
    sb.append(")");
    return sb.toString();
  }
}

interface Expression { }

class Value implements Expression {
  int value;

  Value(int value) {
    this.value = value;
  }

  public String toString() {
    return "Value(" + value + ")";
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

enum BinaryOp { Minus, Divide, Remainder }

class AssocExp implements Expression {
  AssocOp op;
  Expression[] es;

  AssocExp(AssocOp op, Expression[] es) {
    this.op = op;
    this.es = es;
  }

  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("AssocExp(");
    sb.append(op);
    sb.append(", [");
    String sep = "";
    for (Expression d : es) {
      sb.append(sep);
      sep = ", ";
      sb.append(d);
    }
    sb.append("])");
    return sb.toString();
  }
}

enum AssocOp { Plus, Times }

