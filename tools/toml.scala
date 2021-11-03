package afp


import isabelle._

import scala.collection.immutable.ListMap
import scala.util.matching.Regex
import scala.util.parsing.combinator.Parsers
import scala.util.parsing.combinator.lexical.Scanners
import scala.util.parsing.input.CharArrayReader.EofCh

import java.time.{LocalDate, LocalDateTime, LocalTime, OffsetDateTime}


object TOML
{
  type Key = String
  type V = Any

  type T = Map[Key, V]
  object T
  {
    def apply(entries: (Key, V)*): T = ListMap(entries: _*)
    def apply(entries: List[(Key, V)]): T = ListMap(entries: _*)

    def unapply(t: Map[_, V]): Option[T] = {
      if (t.keys.forall(_.isInstanceOf[Key])) Some(t.asInstanceOf[T])
      else None
    }
  }


  /* lexer */

  object Kind extends Enumeration
  {
    val KEYWORD, IDENT, STRING, INTEGER, FLOAT, DATE, ERROR = Value
  }

  sealed case class Token(kind: Kind.Value, text: String)
  {
    def is_ident: Boolean = kind == Kind.IDENT
    def is_keyword(name: String): Boolean = kind == Kind.KEYWORD && text == name
    def is_string: Boolean = kind == Kind.STRING
    def is_integer: Boolean = kind == Kind.INTEGER
    def is_float: Boolean = kind == Kind.FLOAT
    def is_date: Boolean = kind == Kind.DATE
    def is_error: Boolean = kind == Kind.ERROR
  }

  object Lexer extends Scanners with Scan.Parsers
  {
    override type Elem = Char
    type Token = TOML.Token

    def errorToken(msg: String): Token = Token(Kind.ERROR, msg)

    val white_space: String = " \t\n\r"
    override val whiteSpace: Regex = ("[" + white_space + "]+").r
    def whitespace: Parser[Any] = many(character(white_space.contains(_)))

    val letter: Parser[String] = one(character(Symbol.is_ascii_letter))
    val letters1: Parser[String] = many1(character(Symbol.is_ascii_letter))

    def digits: Parser[String] = many(character(Symbol.is_ascii_digit))
    def digits1: Parser[String] = many1(character(Symbol.is_ascii_digit))
    def digitsn(n: Int): Parser[String] = repeated(character(Symbol.is_ascii_digit), n, n)

    def chars(chars: String, num: Int = 1, rep_min: Int = 1, rep_max: Int = 1): Parser[String] =
    {
      chars.toList match {
        case Nil => error("No chars given")
        case c :: Nil => repeated(character(_ == c), num * rep_min, num * rep_max)
        case _ => repeated(character(chars.contains(_)), num * rep_min, num * rep_max)
      }
    }


    /* keyword */

    def keyword: Parser[Token] =
      ("true" | "false" | "[[" | "]]" | chars("{}[],=.")) ^^ (s => Token(Kind.KEYWORD, s))


    /* identifier */

    def ident: Parser[Token] =
      letters1 ^^ (s => Token(Kind.IDENT, s))


    /* string */

    def basic_string: Parser[Token] =
      '\"' ~> rep(string_body) <~ '\"' ^^ (cs => Token(Kind.STRING, cs.mkString))

    def multiline_basic_string: Parser[Token] =
      "\"\"\"" ~>!
        rep(multiline_string_body | chars("\"", rep_max = 2) ~ multiline_string_body) <~
        "\"\"\"" ^^
          (cs => Token(Kind.STRING, cs.mkString.stripPrefix("\n")))

    def multiline_string_body: Parser[Char] =
      elem("", c => c == '\t' || c == '\n' || c == '\r' || (c > '\u001f' && c != '\"' && c != '\\' && c != EofCh)) |
        '\\' ~> string_escape

    def string_body: Parser[Char] =
      elem("", c => c > '\u001f' && c != '\"' && c != '\\' && c != EofCh) | '\\' ~> string_escape

    def string_escape: Parser[Char] =
      elem("", "\"\\/".contains(_)) |
        elem("", "bfnrt".contains(_)) ^^
          { case 'b' => '\b' case 'f' => '\f' case 'n' => '\n' case 'r' => '\r' case 't' => '\t' } |
        'u' ~> repeated(character("0123456789abcdefABCDEF".contains(_)), 4, 4) ^^
          (s => Integer.parseInt(s, 16).toChar)

    def string_failure: Parser[Token] = '\"' ~> failure("Unterminated string")


    /* numbers */

    def integer: Parser[Token] = ("0" ~> letter) ^^ (c => errorToken("Unsupported number format: " + quote(c))) |
      integer_body ^^ (i => Token(Kind.INTEGER, i))

    def integer_body: Parser[String] = zero | opt("-" | "+") ~ nonzero ~ digits ^^
      { case a ~ b ~ c => a.getOrElse("") + b + c }

    def zero: Parser[String] = one(character(c => c == '0'))
    def nonzero: Parser[String] = one(character(c => c != '0' && Symbol.is_ascii_digit(c)))

    def float: Parser[Token] = integer_body ~ opt(number_fract) ~ opt(number_exp) ^^
      { case a ~ b ~ c => Token(Kind.FLOAT, a + b.getOrElse("") + c.getOrElse("")) }

    def number_fract: Parser[String] = "." ~ digits1 ^^ { case a ~ b => a + b }

    def number_exp: Parser[String] =
      one(character("eE".contains(_))) ~ maybe(character("-+".contains(_))) ~ digits1 ^^
        { case a ~ b ~ c => a + b + c }


    /* date and time (simplified) */

    def local_date: Parser[Token] =
      (digitsn(4) <~ '-') ~ (digitsn(2) <~ '-') ~ digitsn(2) ^^
        { case year ~ month ~ day => Token(Kind.DATE, year + "-" + month + "-" + day) }


    /* token */

    def token: Parser[Token] =
      keyword | ident | local_date | (multiline_basic_string | basic_string |
        (string_failure | (integer | float | failure("Illegal character"))))
  }


  /* parser */

  trait Parser extends Parsers
  {
    type Elem = Token

    private object T
    {
      def unapply(table: List[(List[Key], V)]): Option[T] = {
        val by_first_key = table.foldLeft(ListMap.empty[Key, List[(List[Key], V)]]) {
          case (map, (k :: ks, v)) => map.updatedWith(k) {
            case Some(value) => Some(value :+ (ks, v))
            case None => Some(List((ks, v)))
          }
          case _ => return None
        }

        val res = by_first_key.map {
          case (k, (Nil, v) :: Nil) => k -> v
          case (k, T(map)) => k -> map
          case _ => return None
        }

        Some(res)
      }
    }
    private def to_map: PartialFunction[List[(List[Key], V)], T] = { case T(map) => map }


    def $$$(name: String): Parser[Token] = elem(name, _.is_keyword(name))
    def ident: Parser[String] = elem("ident", _.is_ident) ^^ (_.text)
    def string: Parser[String] = elem("string", _.is_string) ^^ (_.text)
    def date: Parser[LocalDate] = elem("date", _.is_date) ^^ (tok => LocalDate.parse(tok.text))
    def integer: Parser[Int] = elem("integer", _.is_integer) ^^ (tok => tok.text.toInt)
    def float: Parser[Double] = elem("float", _.is_float) ^^ (tok => tok.text.toDouble)

    def boolean: Parser[Boolean] = $$$("false") ^^^ false | $$$("true") ^^^ true

    def keys: Parser[List[Key]] = rep1sep(ident | string, $$$("."))


    /* inline values */

    def inline_array: Parser[V] = $$$("[") ~>! rep(toml_value <~ $$$(",")) <~ $$$("]")
    def inline_table: Parser[V] = $$$("{") ~>! (content ^? to_map) <~ $$$("}")
    def toml_value: Parser[V] = date | integer | float | string | boolean | inline_array | inline_table

    /* non-inline arrays */

    def toml_array: Parser[T] =
      $$$("[[") ~>! (keys <~ $$$("]]")) >> { ks =>
        repsep(content ^^ to_map, $$$("[[") ~! (keys ^? { case ks1 if ks1 == ks => }) ~ $$$("]]")) ^^
          { list => List(ks -> list) } ^? to_map
      }


    /* tables */

    private def content: Parser[List[(List[Key], V)]] = rep((keys <~ $$$("=")) ~! toml_value ^^
      { case ks ~ v => ks -> v })

    def toml_table: Parser[T] = $$$("[") ~>! (keys <~ $$$("]")) ~! content ^^
      { case base ~ T(map) => to_map(List(base -> map)) }

    object Merge
    {
      private def merge(map1: T, map2: T): Option[T] =
      {
        val res2 = map2.map {
          case (k2, v2) =>
            map1.get(k2) match {
              case Some(v1) => (v1, v2) match {
                case (TOML.T(t1), TOML.T(t2)) => k2 -> merge(t1, t2).getOrElse(return None)
                case x => return None
              }
              case None => k2 -> v2
            }
          }
        Some(map1.filter { case (k, _) => !map2.contains(k) } ++ res2)
      }
      def unapply(maps: List[T]): Option[T] = Some(maps.fold(Map.empty)(merge(_, _).getOrElse(return None)))
    }

    def root_table: Parser[T] = (content ~ rep(toml_table | toml_array)) ^?
      { case T(map) ~ maps => map :: maps } ^? { case Merge(map) => map }


    def parse(input: CharSequence): T =
    {
      val scanner = new Lexer.Scanner(Scan.char_reader(input))
      phrase(root_table)(scanner) match {
        case Success(toml, _) => toml
        case NoSuccess(_, next) => error("Malformed TOML input at " + next.pos)
      }
    }
  }

  object Parser extends Parser


  /* standard format */

  def parse(s: String): T = Parser.parse(s)

  /* format to a subset of TOML */

  object Format
  {
    def apply(toml: T): String =
    {
      val result = new StringBuilder

      /* keys */

      def key(k: Key): Unit =
      {
        val Bare_Key = """[A-Za-z0-9_-].+""".r
        k match {
          case Bare_Key() => result ++= k
          case _ =>
            result += '"'
            result ++= k
            result += '"'
        }
      }

      def keys(ks: List[Key]): Unit =
        Library.separate(None, ks.reverse.map(Some(_))).foreach {
          case None => result += '.'
          case Some(k) => key(k)
        }

      /* string */

      def basic_string(s: String): Unit =
      {
        result += '"'
        result ++=
          s.iterator.map {
            case '\b' => "\\b"
            case '\t' => "\\t"
            case '\n' => "\\n"
            case '\f' => "\\f"
            case '\r' => "\\r"
            case '"'  => "\\\""
            case '\\' => "\\\\"
            case c =>
              if (c <= '\u001f' || c == '\u007f') "\\u%04x".format(c.toInt)
              else c
          }.mkString
        result += '"'
      }

      def multiline_basic_string(s: String): Unit =
      {
        result ++= "\"\"\"\n"
        result ++=
          s.iterator.map {
            case '\b' => "\\b"
            case '\t' => "\t"
            case '\n' => "\n"
            case '\f' => "\\f"
            case '\r' => "\r"
            case '"'  => "\\\""
            case '\\' => "\\\\"
            case c =>
              if (c <= '\u001f' || c == '\u007f') "\\u%04x".format(c.toInt)
              else c
          }.mkString.replace("\"\"\"", "\"\"\\\"")
        result ++= "\"\"\""
      }

      /* integer, boolean, offset date-time, local date-time, local date, local time */

      object To_String
      {
        def unapply(v: V): Option[String] = v match {
          case _: Int | _: Double | _: Boolean | _: OffsetDateTime |
               _: LocalDateTime | _: LocalDate | _: LocalTime => Some(v.toString)
          case _ => None
        }
      }

      /* inline: string, float, To_String, value array */

      def inline(v: V, indent: Int = 0): Unit =
      {
        def indentation(i: Int): Unit = for (_ <- Range(0, i)) result ++= "  "

        indentation(indent)
        v match {
          case s: String =>
            if (s.contains("\n") && s.length > 20) multiline_basic_string(s)
            else basic_string(s)
          case To_String(s) =>
            result ++= s
          case list: List[V] =>
            if (list.isEmpty) {
              result ++= "[]"
            } else {
              result ++= "[\n"
              list.foreach { elem =>
                inline(elem, indent + 1)
                result ++= ",\n"
              }
              indentation(indent)
              result += ']'
            }
          case _ => error("Not inline TOML value: " + v.toString)
        }
      }

      /* array */

      def inline_values(path: List[Key], v: V): Unit =
      {
        v match {
          case T(map) => map.foreach { case (k, v1) => inline_values(k :: path, v1) }
          case _ =>
            keys(path)
            result ++= " = "
            inline(v)
            result += '\n'
        }
      }

      def is_inline(elem: V): Boolean = elem match {
        case To_String(_) | _: Double | _: String => true
        case list: List[V] => list.forall(is_inline)
        case _ => false
      }

      def array(path: List[Key], list: List[V]): Unit =
      {
        if (list.forall(is_inline)) inline_values(path.take(1), list)
        else {
          list.collect {
            case T(map) =>
              result ++= "\n[["
              keys(path)
              result ++= "]]\n"
              table(path, map, is_table_entry = true)
            case _ => error("Array can only contain either all tables or all non-tables")
          }
        }
      }

      /* table */

      def table(path: List[Key], map: T, is_table_entry: Boolean = false): Unit =
      {
        val (values, nodes) = map.toList.partition(kv => is_inline(kv._2))

        if (!is_table_entry && path.nonEmpty) {
          result ++= "\n["
          keys(path)
          result ++= "]\n"
        }

        values.foreach { case (k, v) => inline_values(List(k), v) }

        nodes.foreach {
          case (k, T(map1)) => table(k :: path, map1)
          case (k, list: List[V]) => array(k :: path, list)
          case (_, v) => error("Invalid TOML: " + v.toString)
        }
      }

      table(Nil, toml)
      result.toString
    }
  }
}
