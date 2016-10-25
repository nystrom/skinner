package skinner.util;

public class Tuple3<A, B, C> {
  public final A fst;
  public final B snd;
  public final C thd;

  public Tuple3(A fst, B snd, C thd) {
    this.fst = fst;
    this.snd = snd;
    this.thd = thd;
  }
}
