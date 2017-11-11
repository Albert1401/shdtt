import FunsAndTypes._

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.io.Source

object HW3 {

  def unq(v: Variable, qtype: SimpleType): SimpleType = {
    def f(ex: SimpleType): (SimpleType, Map[Var, Var]) = ex match {
      case QAll(qv, e) => {
        val (e_, mp_) = f(e)
        e_ -> (mp_ + (qv -> newVar))
      }
      case e_ => (e_, Map.empty)
    }

    val (expr, mp) = f(qtype)
    subst(mp, expr)
  }

  def closure(expr: SimpleType): SimpleType = {
    def freeVars(e: SimpleType, bounded: Set[Var]): Set[Var] = {
      e match {
        case QAll(v, s) => freeVars(s, bounded + v)
        case Impl(l, r) => freeVars(l, bounded) ++ freeVars(r, bounded)
        case v@Var(_) if bounded.contains(v) => Set.empty
        case v@Var(_) => Set.empty + v
      }
    }

    val vars = freeVars(expr, Set.empty)
    var res = expr
    for (v <- vars) {
      res = QAll(v, res)
    }
    res
  }

  def W(g: Map[Variable, SimpleType], expr: LambdaExpression): (SimpleType => SimpleType, SimpleType) = {
    expr match {
      case Application(l, r) =>
        val (s1, t1) = W(g, l)
        val (s2, t2) = W(g map { case (v: Variable, t: SimpleType) => v -> s1(t) }, r)
        val ab = new ArrayBuffer[(SimpleType, SimpleType)]()
        val b = newVar
        ab += (s2(t1) -> Impl(t2, b))
        val v = solveSystem(ab)
        val s = (t: SimpleType) => v(s1(s2(t)))
        (s, s(b))

      case Abstraction(v, e) =>
        val b = newVar
        val (s, t) = W(g + (v -> b), e)
        (s, Impl(s(b), t))

      case LetIn(v, arg, e) =>
        val (s1, t1) = W(g, arg)

        val s1gx = (g - v) map { case (v1: Variable, t: SimpleType) => v1 -> s1(t) }


        val xqized = s1(closure(t1))

        val (s2, t2) = W(s1gx + (v -> xqized), e)
        ((x: SimpleType) => s2(s1(x)), t2)

      case v@Variable(_, _) if g.contains(v) =>
        (a => a, unq(v, g(v)))

      case _ => throw new RuntimeException("Лямба-выражение не имеет типа")
    }
  }

  def main(args: Array[String]): Unit = {
    try {
      val (expr, rmap) = makeVarsUnique(LambdaPackratParser.parse(Source.fromFile("task3.in").mkString).get)
      val initg = getFreeVars(Set.empty, expr).map(v => v -> newVar).toMap

      val (sbst, t) = W(initg, expr)
      println(sbst(t))
      for ((v, t) <- initg) {
        println(rmap(v) ++ " : " ++ sbst(t).toString)
      }
    } catch {
      case e: RuntimeException => println(e.getMessage)
    }
  }
}
