import FunsAndTypes._

import scala.util.parsing.combinator._
import scala.util.parsing.input.CharSequenceReader
//import scalaz.Need

object LambdaPackratParser extends RegexParsers with PackratParsers {

  override val skipWhitespace = true

  lazy val ws = "[ \t\n\r]".r

  lazy val A: PackratParser[LambdaExpression] = {
    val a = "let" ~ name ~ "=" ~ A ~ "in" ~ A ^^ {
      case _ ~ s ~ _ ~ arg ~ _ ~ e => LetIn(Variable(s,0), arg, e)
    }
    val b = E ^^ { e => e}
    a | b
  }

  lazy val E: PackratParser[LambdaExpression] = {
    val a = T ~ "\\" ~ name ~ "." ~ E ^^ { case t ~ _ ~ n ~ _ ~ e => Application(t, Abstraction(Variable(n, 0), e)) }
    val b = "\\" ~ name ~ "." ~ E ^^ { case _ ~ n ~ _ ~ e => Abstraction(Variable(n, 0), e) }
    val c = T ^^ { t => t }
    a | b | c
  }

  lazy val T: PackratParser[LambdaExpression] = T ~ F ^^ { case t ~ f => Application(t, f) } | F ^^ (f => f)


  lazy val F: PackratParser[LambdaExpression] = {
    val a = name ^^ (s => Variable(s, 0))
    val b = "(" ~ A ~ ")" ^^ { case _ ~ e ~ _ => e }
    a | b
  }

  lazy val name: PackratParser[String] = "(?!let)(?!in)[a-z][a-z0-9]*".r ^^ { n => n }


  def parse(input: String) = parseAll(A, new PackratReader(new CharSequenceReader(input)))
}
