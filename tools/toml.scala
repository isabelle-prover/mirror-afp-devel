/* Author: Fabian Huch, TU Muenchen

Support for TOML: https://toml.io/en/v1.0.0
 */
package afp


import isabelle.*

import java.lang.Long.parseLong
import java.time.{LocalDate, LocalDateTime, LocalTime, OffsetDateTime}

import scala.collection.immutable.ListMap
import scala.reflect.{ClassTag, classTag}
import scala.util.Try
import scala.util.matching.Regex
import scala.util.parsing.combinator
import scala.util.parsing.combinator.lexical.Scanners
import scala.util.parsing.input.CharArrayReader.EofCh


object TOML {
  type Key = String
  type V = Any

  type T = Map[Key, V]

  object T {
    def apply(entries: (Key, V)*): T = ListMap(entries: _*)

    def apply(entries: List[(Key, V)]): T = ListMap(entries: _*)

    def unapply(t: Map[_, V]): Option[T] = {
      if (t.keys.forall(_.isInstanceOf[Key])) Some(t.asInstanceOf[T]) else None
    }
  }


  /* typed access */

  def split_as[A: ClassTag](map: T): List[(Key, A)] =
    map.keys.toList.map(k => k -> get_as[A](map, k))

  def optional_as[A: ClassTag](map: T, name: String): Option[A] = map.get(name) match {
    case Some(value: A) => Some(value)
    case Some(value) =>
      error("Value " + quote(value.toString) + " not of type " + classTag[A].runtimeClass.getName)
    case None => None
  }

  def get_as[A: ClassTag](map: T, name: String): A = map.get(name) match {
    case Some(value: A) => value
    case Some(value) =>
      error("Value " + quote(value.toString) + " not of type " + classTag[A].runtimeClass.getName)
    case None => error("Field " + name + " not in " + commas_quote(map.keys))
  }


  /* lexer */

  object Kind extends Enumeration {
    val KEYWORD, VALUE, STRING, MULTILINE_STRING, LINE_SEP, ERROR = Value
  }

  sealed case class Token(kind: Kind.Value, text: String) {
    def is_keyword(name: String): Boolean = kind == Kind.KEYWORD && text == name
    def is_value: Boolean = kind == Kind.VALUE
    def is_string: Boolean = kind == Kind.STRING
    def is_multiline_string: Boolean = kind == Kind.MULTILINE_STRING
    def is_line_sep: Boolean = kind == Kind.LINE_SEP
  }

  object Lexer extends Scanners with Scan.Parsers {
    override type Elem = Char
    type Token = TOML.Token

    def errorToken(msg: String): Token = Token(Kind.ERROR, msg)

    val white_space: String = " \t"
    override val whiteSpace: Regex = ("[" + white_space + "]+").r
    override def whitespace: Parser[Any] = rep(comment | many1(character(white_space.contains(_))))

    def line_sep: Parser[String] = rep1("\n" | s"\r\n" | EofCh) ^^ (cs => cs.mkString)
    def line_sep_token: Parser[Token] = line_sep ^^ (s => Token(Kind.LINE_SEP, s))

    def is_control(e: Elem): Boolean =
      e <= '\u0008' || ('\u000A' <= e && e <= '\u001F') || e == '\u007F'

    override def comment: Parser[String] = '#' ~>! many(character(c => !is_control(c)))

    def keyword: Parser[Token] = one(character("{}[],=.".contains)) ^^ (s => Token(Kind.KEYWORD, s))

    def is_value(c: Elem): Boolean =
      Symbol.is_ascii_letter(c) || Symbol.is_ascii_digit(c) || "_-:+".contains(c)
    def value: Parser[Token] =
      many1(character(is_value)) ~
        opt(' ' ~ many1(character(is_value)) ^^ { case ws ~ s => ws.toString + s }) ~
        opt('.' ~ many1(character(is_value)) ^^ { case dot ~ s => dot.toString + s}) ^^
        { case s ~ ss ~ sd => Token(Kind.VALUE, s + ss.getOrElse("") + sd.getOrElse("")) }

    def string: Parser[Token] =
      multiline_basic_string | basic_string | multiline_literal_string | literal_string

    private def trim(s: String): String =
      if (s.startsWith("\n")) s.stripPrefix("\n") else s.stripPrefix("\r\n")

    def basic_string: Parser[Token] =
      '"' ~> rep(basic_string_elem) <~ '"' ^^ (cs => Token(Kind.STRING, cs.mkString))

    def multiline_basic_string: Parser[Token] =
      "\"\"\"" ~>
        rep(multiline_basic_string_elem |
          ("\"\"" | "\"") ~ multiline_basic_string_elem ^^ { case s ~ t => s + t }) ~
        repeated(character(_ == '"'), 3, 5) ^^ { case cs ~ q =>
          Token(Kind.MULTILINE_STRING, trim(cs.mkString + q.drop(3))) }

    private def multiline_basic_string_elem: Parser[String] =
      ('\\' ~ line_sep ~ rep(many1(character(white_space.contains)) | line_sep)) ^^ (_ => "") |
        basic_string_elem ^^ (_.toString) | line_sep

    def literal_string: Parser[Token] =
      '\'' ~> rep(literal_string_elem) <~ '\'' ^^ (cs => Token(Kind.STRING, cs.mkString))

    def multiline_literal_string: Parser[Token] =
      "'''" ~>
        rep(multiline_literal_string_elem |
          ("''" | "'") ~ multiline_literal_string_elem ^^ { case s ~ t => s + t }) ~
        repeated(character(_ == '\''), 3, 5) ^^ { case cs ~ q =>
          Token(Kind.MULTILINE_STRING, trim(cs.mkString + q.drop(3))) }

    private def multiline_literal_string_elem: Parser[String] =
      line_sep | literal_string_elem ^^ (_.toString)

    private def basic_string_elem: Parser[Elem] =
      elem("", c => !is_control(c) && !"\"\\".contains(c)) | '\\' ~> string_escape

    private def string_escape: Parser[Elem] =
      elem("", "\"\\".contains(_)) |
        elem("", "btnfr".contains(_)) ^^
          { case 'b' => '\b' case 't' => '\t' case 'n' => '\n' case 'f' => '\f' case 'r' => '\r' } |
        ('u' ~> repeated(character("0123456789abcdefABCDEF".contains(_)), 4, 4) |
          'U' ~> repeated(character("0123456789abcdefABCDEF".contains(_)), 8, 8)) ^^
          (s => Integer.parseInt(s, 16).toChar)

    private def literal_string_elem: Parser[Elem] = elem("", c => !is_control(c) && c != '\'')

    def string_failure: Parser[Token] = ("\"" | "'") ~> failure("Unterminated string")

    def token: Parser[Token] =
      line_sep_token | keyword | value | string | string_failure | failure("Unrecognized token")
  }


  /* parser */

  trait Parsers extends combinator.Parsers {
    type Elem = Token

    def key: Parser[List[Key]] = rep1sep(keys, $$$(".")) ^^ (_.flatten)


    /* values */

    def string: Parser[String] =
      elem("string", e => e.is_string || e.is_multiline_string) ^^ (_.text)
    def integer: Parser[Long] = decimal_int | binary_int | octal_int | hexadecimal_int
    def float: Parser[Double] = symbol_float | number_float
    def boolean: Parser[Boolean] = token("boolean", _.is_value, Value.Boolean.parse)

    def offset_date_time: Parser[OffsetDateTime] =
      token("offset date-time", _.is_value, s => OffsetDateTime.parse(s.replace(" ", "T")))
    def local_date_time: Parser[LocalDateTime] =
      token("local date-time", _.is_value, s => LocalDateTime.parse(s.replace(" ", "T")))
    def local_date: Parser[LocalDate] = token("local date", _.is_value, LocalDate.parse)
    def local_time: Parser[LocalTime] = token("local time", _.is_value, LocalTime.parse)

    def array: Parser[V] =
      $$$("[") ~>! repsep(opt(line_sep) ~> toml_value, opt(line_sep) ~ $$$(",")) <~!
        opt(line_sep) ~! opt($$$(",")) ~! opt(line_sep) <~! $$$("]")

    def inline_table: Parser[V] = $$$("{") ~>! (repsep(pair, $$$(",")) ^? to_map) <~! $$$("}")


    /* structures */

    def pair: Parser[(List[Key], V)] = (key <~! $$$("=")) ~! toml_value ^^ { case ks ~ v => (ks,v) }

    def table: Parser[T] = $$$("[") ~> (key <~! $$$("]") ~! line_sep) ~! content ^?
      { case base ~ T(map) => to_map(List(base -> map)) }

    def array_of_tables: Parser[T] =
      $$$("[") ~ $$$("[") ~>! (key <~! $$$("]") ~! $$$("]") ~! line_sep) >> { ks =>
        repsep(content ^^ to_map, $$$("[") ~ $$$("[") ~ (key ^? { case ks1 if ks1 == ks => }) ~!
          $$$("]") ~! $$$("]") ~! line_sep) ^^
          { list => List(ks -> list) } ^? to_map
      }

    def toml: Parser[T] =
      (opt(line_sep) ~> content ~ rep(table | array_of_tables)) ^?
        { case T(map) ~ maps => map :: maps } ^? { case Merge(map) => map } |
      (opt(line_sep) ~>! content) ^? { case T(map) => map }


    /* auxiliary */

    private def $$$(name: String): Parser[Token] = elem(name, _.is_keyword(name))
    private def maybe[A, B](p: Parser[A], f: A => B): Parser[B] =
      p ^^ (a => Try(f(a))) ^? { case util.Success(v) => v}
    private def token[A](name: String, p: Token => Boolean, parser: String => A): Parser[A] =
      maybe(elem(name, p), s => parser(s.text))
    private def prefixed[A](
      prefix: String, name: String, p: String => Boolean, parser: String => A
    ): Parser[A] =
      token(name, e => e.is_value && e.text.startsWith(prefix) && p(e.text.stripPrefix(prefix)),
        s => parser(s.stripPrefix(prefix)))

    private def is_key(e: Elem): Boolean = e.is_value && !e.text.exists("+: ".contains(_))
    private def keys: Parser[List[Key]] =
      token("string key", _.is_string, List(_)) | token("key", is_key, _.split('.').toList)

    private def sep_surrounded(s: String): Boolean =
      !s.startsWith("_") && !s.endsWith("_") && s.split('_').forall(_.nonEmpty)
    private def no_leading_zero(s: String): Boolean = {
      val t = s.replaceAll("_", "").takeWhile(_.isDigit)
      t == "0" || !t.startsWith("0")
    }

    private def is_int(s: String): Boolean =
      no_leading_zero(s.replaceAll("[-+]", "")) && sep_surrounded(s.replaceAll("[-+]", ""))
    private def decimal_int: Parser[Long] =
      token("integer", e => e.is_value && is_int(e.text), _.replace("_", "").toLong)
    private def binary_int: Parser[Long] =
      prefixed("0b", "integer", sep_surrounded, s => parseLong(s.replace("_", ""), 2))
    private def octal_int: Parser[Long] =
      prefixed("0o", "integer", sep_surrounded, s => parseLong(s.replace("_", ""), 8))
    private def hexadecimal_int: Parser[Long] =
      prefixed("0x", "integer", sep_surrounded, s => parseLong(s.replace("_", ""), 16))

    private def is_float(s: String): Boolean =
      s.exists(".eE".contains) && s.count("eE".contains) <= 1 &&
        no_leading_zero(s.replaceAll("[-+]", "")) &&
        sep_surrounded(s.replaceAll("[-+]", "").replaceAll("[.eE][+\\-]?", "_"))
    private def number_float: Parser[Double] =
      token("float", e => e.is_value && is_float(e.text), _.replace("_", "").toDouble)
    private def symbol_float: Parser[Double] =
      token("float", _.is_value, {
        case "inf" | "+inf" => Double.PositiveInfinity
        case "-inf" => Double.NegativeInfinity
        case "nan" | "+nan" | "-nan" => Double.NaN
      })

    private def toml_value: Parser[V] = string | float | integer | boolean | offset_date_time |
      local_date_time | local_date | local_time | array | inline_table

    private def line_sep: Parser[Any] = rep1(elem("line sep", _.is_line_sep))

    private def content: Parser[List[(List[Key], V)]] =
      rep((key <~! $$$("=")) ~! toml_value <~! line_sep ^^ { case ks ~ v => ks -> v })


    /* extractors */

    private object T {
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

    object Merge {
      private def merge(map1: T, map2: T): Option[T] = {
        val res2 = map2.map {
          case (k2, v2) =>
            map1.get(k2) match {
              case Some(v1) => (v1, v2) match {
                case (TOML.T(t1), TOML.T(t2)) => k2 -> merge(t1, t2).getOrElse(return None)
                case _ => return None
              }
              case None => k2 -> v2
            }
        }
        Some(map1.filter { case (k, _) => !map2.contains(k) } ++ res2)
      }

      def unapply(maps: List[T]): Option[T] =
        Some(maps.fold(Map.empty)(merge(_, _).getOrElse(return None)))
    }


    /* parse */

    def parse(input: String): T = {
      val scanner = new Lexer.Scanner(Scan.char_reader(input + EofCh))
      val result = phrase(toml)(scanner)
      result match {
        case Success(toml, _) => toml
        case Failure(msg, next) => error("Malformed TOML input at " + next.pos + ": " + msg)
        case Error(msg, next) => error("Error parsing toml at " + next.pos + ": " + msg)
      }
    }
  }

  object Parsers extends Parsers

  def parse(s: String): T = Parsers.parse(s)


  /* format to a subset of TOML */

  object Format {
    def apply(toml: T): String = {
      val result = new StringBuilder

      /* keys */

      def key(k: Key): Unit = {
        val Bare_Key = """[A-Za-z0-9_-]+""".r
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

      def basic_string(s: String): Unit = {
        result += '"'
        result ++=
          s.iterator.map {
            case '\b' => "\\b"
            case '\t' => "\\t"
            case '\n' => "\\n"
            case '\f' => "\\f"
            case '\r' => "\\r"
            case '"' => "\\\""
            case '\\' => "\\\\"
            case c =>
              if (c <= '\u001f' || c == '\u007f') "\\u%04x".format(c.toInt)
              else c
          }.mkString
        result += '"'
      }

      def multiline_basic_string(s: String): Unit = {
        result ++= "\"\"\"\n"
        result ++=
          s.iterator.map {
            case '\b' => "\\b"
            case '\t' => "\t"
            case '\n' => "\n"
            case '\f' => "\\f"
            case '\r' => "\r"
            case '"' => "\\\""
            case '\\' => "\\\\"
            case c =>
              if (c <= '\u001f' || c == '\u007f') "\\u%04x".format(c.toInt)
              else c
          }.mkString.replace("\"\"\"", "\"\"\\\"")
        result ++= "\"\"\""
      }

      /* integer, boolean, offset date-time, local date-time, local date, local time */

      object To_String {
        def unapply(v: V): Option[String] = v match {
          case _: Int | _: Double | _: Boolean | _: OffsetDateTime |
               _: LocalDateTime | _: LocalDate | _: LocalTime => Some(v.toString)
          case _ => None
        }
      }

      /* inline: string, float, To_String, value array */

      def `inline`(v: V, indent: Int = 0): Unit = {
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
                `inline`(elem, indent + 1)
                result ++= ",\n"
              }
              indentation(indent)
              result += ']'
            }
          case _ => error("Not inline TOML value: " + v.toString)
        }
      }

      /* array */

      def inline_values(path: List[Key], v: V): Unit = {
        v match {
          case T(map) => map.foreach { case (k, v1) => inline_values(k :: path, v1) }
          case _ =>
            keys(path)
            result ++= " = "
            `inline`(v)
            result += '\n'
        }
      }

      def is_inline(elem: V): Boolean = elem match {
        case To_String(_) | _: Double | _: String => true
        case list: List[V] => list.forall(is_inline)
        case _ => false
      }

      def array(path: List[Key], list: List[V]): Unit = {
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

      def table(path: List[Key], map: T, is_table_entry: Boolean = false): Unit = {
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
