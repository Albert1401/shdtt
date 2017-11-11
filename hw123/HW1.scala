
import FunsAndTypes._

import scala.collection.mutable
import scala.io.Source

object HW1 {

  var uniqn = 0

  def reduction(expr: LambdaExpression): Option[LambdaExpression] = expr match {
    case Application(l, r) =>
      l match {
        case Abstraction(v, e) => Some(substitute(v, r, e))
        case _ => reduction(l) match {
          case Some(l_) => Some(Application(l_, r))
          case None =>
            reduction(r) match {
              case Some(r_) => Some(Application(l, r_))
              case None => None
            }
        }
      }

    case Abstraction(v, e) => reduction(e) match {
      case Some(e_) => Some(Abstraction(v, e_))
      case _ => None
    }
    case _ => None
  }

  def substitute(v: Variable, arg: => LambdaExpression, expr: LambdaExpression): LambdaExpression = {
    def f(e: LambdaExpression): LambdaExpression = {
      e match {
        case Application(l, r) => Application(f(l), f(r))
        case Abstraction(v_, r) => Abstraction(v_, f(r))
        case (v_ @Variable(_, _)) if v == v_ => rename(arg)
        case (v_ @Variable(_, _)) => v_
      }
    }

    f(expr)
  }

  def rename(expr: LambdaExpression): LambdaExpression = {
    val mp: mutable.Map[Variable, Variable] = new mutable.HashMap[Variable, Variable]
    val vars: mutable.Set[Variable] = new mutable.HashSet[Variable]

    getAbstractedVars1(expr, vars)

    for (v <- vars) {
      uniqn += 1
      mp.put(v, Variable(v.s, uniqn))
    }

    def f(e: LambdaExpression): LambdaExpression = {
      e match {
        case Application(l, r) => Application(f(l), f(r))
        case Abstraction(v, e_) => Abstraction(f(v).asInstanceOf[Variable], f(e_))
        case (v@(Variable(_, _))) if mp.contains(v) => mp(v)
        case (v@(Variable(_, _))) => v
      }
    }

    f(expr)
  }

  def getAbstractedVars1(expr: LambdaExpression, set: mutable.Set[Variable]): Unit = {
    expr match {
      case Abstraction(v, e) =>
        set.add(v)
        getAbstractedVars1(e, set)

      case Application(l, r) =>
        getAbstractedVars1(l, set)
        getAbstractedVars1(r, set)

      case _ =>
    }
  }

  def main(args: Array[String]): Unit = {
    var e = LambdaPackratParser.parse(Source.fromFile("task1.in").mkString).get
    var b = true
    while (b) {
      reduction(e) match {
        case Some(step) => {
          e = step
        }
        case None => b = false
      }
    }
    println(e)
  }

}
