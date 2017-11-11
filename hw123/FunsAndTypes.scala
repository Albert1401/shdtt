import scala.collection.immutable.Stack
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.io.Source

/**
  * Created by clitcommander on 8/30/17.
  */
object FunsAndTypes {
  var uniq = 0


  trait LambdaExpression
  case class Application(l: LambdaExpression, r: LambdaExpression) extends LambdaExpression {
    override def toString = "(" ++ l.toString ++ " " ++ r.toString ++ ")"
  }

  case class Abstraction(v: Variable, e: LambdaExpression) extends LambdaExpression {
    override def toString = "(\\" ++ v.toString ++ "." ++ e.toString ++ ")"
  }

  case class Variable(s: String, n: Int) extends LambdaExpression {
    override def toString = s ++ n.toString
  }

  case class LetIn(v : Variable, arg : LambdaExpression, e : LambdaExpression) extends LambdaExpression {
    override def toString = "let " ++ v.toString ++" = " ++ arg.toString ++ " in " ++ e.toString
  }


  trait SimpleType

  case class Var(i: Int) extends SimpleType {
    override def toString: String = "v" ++ i.toString
  }

  case class Impl(l: SimpleType, r: SimpleType) extends SimpleType {
    override def toString: String = "(" ++ l.toString ++ "->" ++ r.toString ++ ")"
  }

  case class QAll(v:Var, e :SimpleType) extends SimpleType {
    override def toString: String = "@" ++ v.toString ++ "." ++ e.toString
  }

  def newVar: Var = {
    uniq += 1
    Var(uniq)
  }

  def getFreeVars(bounded : Set[Variable], expr : LambdaExpression) : Set[Variable]={
    expr match {
      case v @ Variable(_, _) if !bounded.contains(v) => Set.empty + v
      case Application(l, r) => getFreeVars(bounded, l) ++ getFreeVars(bounded, r)
      case Abstraction(v, e) => getFreeVars(bounded + v, e)
      case LetIn(v,arg,e) => getFreeVars(bounded + v, arg) ++ getFreeVars(bounded + v, e)
      case e => Set.empty
    }
  }

  def subst(v: Var, arg: SimpleType, e: SimpleType): SimpleType = {
    e match {
      case v1@Var(_) => if (v1 == v) {
        arg
      } else v1
      case Impl(l, r) => Impl(subst(v, arg, l), subst(v, arg, r))
    }
  }

  def subst(vmap: Map[Var, SimpleType], e: SimpleType): SimpleType = {
    e match {
      case v1@Var(_) => if (vmap.contains(v1)) {
        vmap(v1)
      } else v1
      case Impl(l, r) => Impl(subst(vmap, l), subst(vmap, r))
      case QAll(v, qe) if vmap contains v => throw new RuntimeException("jagajaga")
      case QAll(v, qe)=> QAll(v, subst(vmap, qe))
    }
  }

  def makeVarsUnique(expr: LambdaExpression): (LambdaExpression, Map[Variable, String]) ={
    var varmap = mutable.Map.empty[Variable, String]

    var freevs = mutable.Map.empty[String, Variable]
    def f (e : LambdaExpression, bounded : Map[String, Stack[Variable]]) : LambdaExpression = e match {
      case LetIn(v, arg, le) =>
        val nb = bounded.getOrElse(v.s, Stack.empty[Variable])

        val nv = Variable("v", uniq)
        uniq += 1

        varmap += (nv -> v.s)
        LetIn(nv, f(arg, bounded + (v.s -> nb.push(nv))), f(le, bounded + (v.s -> nb.push(nv))))

      case Abstraction(v, ae) =>
        val nb = bounded.getOrElse(v.s, Stack.empty[Variable])

        val nv = Variable("v", uniq)
        uniq += 1

        varmap += (nv -> v.s)
        Abstraction(nv, f(ae, bounded + (v.s -> nb.push(nv))))

      case Application(l, r) => Application(f(l, bounded), f(r,bounded))

      case Variable(s, _) if bounded.contains(s) && bounded(s).nonEmpty => bounded(s).head

      case Variable(s, _) if freevs.contains(s) => freevs(s)

      case Variable(s, _) =>
        val nv = Variable("v", uniq)
        uniq+=1

        freevs += (s -> nv)
        varmap += (nv -> s)
        nv
    }
    val ne = f(expr, Map.empty)
    (ne, varmap.toMap)
  }

  def solveSystem(sys : ArrayBuffer[(SimpleType, SimpleType)]): (SimpleType => SimpleType) = {
    while (true) {
      var i = 0
      while (i < sys.size) {
        val e = sys(i)
        e match {
          case (im@Impl(_, _), v@Var(_)) => sys(i) = (v, im)
          case (l, r) if l == r =>
            sys(i) = sys.last
            sys.remove(sys.size - 1)
            i -= 1
          case (Impl(ll, lr), Impl(rl, rr)) =>
            sys += ll -> rl
            sys(i) = lr -> rr
          case (v@Var(_), t) =>
            if (in(v, t)) {
              throw new RuntimeException("Лямбда-выражение не имеет типа")
            } else {
              for (j <- sys.indices) {
                if (i != j) {
                  val (l, r) = sys(j)
                  sys(j) = subst(v, t, l) -> subst(v, t, r)
                }
              }
            }
        }
        i += 1
      }

      var ok = true
      ok = ok && sys.forall {
        case (Var(_), _) => true
        case _ => false
      }
      var varset = mutable.Set.empty[Var]
      ok = ok && sys.forall {
        case (v@Var(_), _) => varset.add(v)
      }
      ok = ok && varset.forall { v =>
        sys.forall {
          case (_, r) => !in(v, r)
        }
      }
      if (ok) {
        def f(t : SimpleType) : SimpleType = {
          val mp = sys.map({
            case (a,b) => a.asInstanceOf[Var] -> b
          }).toMap
          subst(mp, t)
        }
        return f
      }
    }
    null
  }

  def in(v: Var, e: SimpleType): Boolean = {
    e match {
      case v1@Var(_) => v == v1
      case Impl(l, r) => in(v, l) || in(v, r)
    }
  }

  def main(args : Array[String]): Unit ={
    val bf = new ArrayBuffer[(SimpleType, SimpleType)]()
    bf.+=(Var(0) -> Var(2))
    bf.+=(Var(0) -> Var(1))
    solveSystem(bf)
  }

}