/* Author: Fabian Huch, TU Muenchen

Support for TOML: https://toml.io/en/v1.0.0
 */
package afp


import isabelle._

import scala.collection.immutable.ListMap
import scala.reflect.{ClassTag, classTag}
import scala.util.Try
import scala.util.matching.Regex
import scala.util.parsing.combinator
import scala.util.parsing.combinator.lexical.Scanners
import scala.util.parsing.input.CharArrayReader.EofCh

import java.time.{LocalDate, LocalDateTime, LocalTime, OffsetDateTime}


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

  def split_as[A: ClassTag](map: T): List[(Key, A)] = map.keys.toList.map(k => k -> get_as[A](map, k))

  def optional_as[A: ClassTag](map: T, name: String): Option[A] = map.get(name) match {
    case Some(value: A) => Some(value)
    case Some(value) => error("Value " + quote(value.toString) + " not of type " + classTag[A].runtimeClass.getName)
    case None => None
  }

  def get_as[A: ClassTag](map: T, name: String): A = map.get(name) match {
    case Some(value: A) => value
    case Some(value) => error("Value " + quote(value.toString) + " not of type " + classTag[A].runtimeClass.getName)
    case None => error("Field " + name + " not in " + commas_quote(map.keys))
  }


  /* lexer */

  object Kind extends Enumeration {
    val KEYWORD, IDENT, STRING, ERROR = Value
  }

  sealed case class Token(kind: Kind.Value, text: String) {
    def is_ident: Boolean = kind == Kind.IDENT
    def is_keyword(name: String): Boolean = kind == Kind.KEYWORD && text == name
    def is_string: Boolean = kind == Kind.STRING
    def is_error: Boolean = kind == Kind.ERROR
  }

  object Lexer extends Scanners with Scan.Parsers {
    override type Elem = Char
    type Token = TOML.Token

    def errorToken(msg: String): Token = Token(Kind.ERROR, msg)

    val white_space: String = " \t\n\r"
    override val whiteSpace: Regex = ("[" + white_space + "]+").r

    override def comment: Parser[String] =
      '#' ~>! rep(elem("", c => c != EofCh && c != '\n' && c != '\r')) ^^ (s => s.mkString)

    override def whitespace: Parser[Any] = rep(comment | many1(character(white_space.contains(_))))

    def keyword: Parser[Token] = ("[[" | "]]" | one(character("{}[],=.".contains(_)))) ^^ (s => Token(Kind.KEYWORD, s))

    def ident: Parser[Token] =
      many1(character(c => Symbol.is_ascii_digit(c) || Symbol.is_ascii_letter(c) || c == '_' || c == '-')) ^^
        (s => Token(Kind.IDENT, s))

    def basic_string: Parser[Token] =
      '\"' ~> rep(string_body) <~ '\"' ^^ (cs => Token(Kind.STRING, cs.mkString))

    def multiline_basic_string: Parser[Token] =
      "\"\"\"" ~>!
        rep(multiline_string_body | ("\"" | "\"\"") ~ multiline_string_body ^^ { case s ~ t => s + t }) <~
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

    def token: Parser[Token] =
      keyword | ident | (multiline_basic_string | basic_string | string_failure) | failure("Illegal character")
  }


  /* parser */

  trait Parsers extends combinator.Parsers {
    type Elem = Token

    def keys: Parser[List[Key]] = rep1sep(key, $$$("."))

    def string: Parser[String] = elem("string", _.is_string) ^^ (_.text)

    def integer: Parser[Int] = token("integer", _.is_ident, _.toInt)

    def float: Parser[Double] = token("float", _.is_ident, _.toDouble)

    def boolean: Parser[Boolean] = token("boolean", _.is_ident, _.toBoolean)

    def offset_date_time: Parser[OffsetDateTime] = token("offset date-time", _.is_ident, OffsetDateTime.parse)

    def local_date_time: Parser[LocalDateTime] = token("local date-time", _.is_ident, LocalDateTime.parse)

    def local_date: Parser[LocalDate] = token("local date", _.is_ident, LocalDate.parse)

    def local_time: Parser[LocalTime] = token("local time", _.is_ident, LocalTime.parse)

    def array: Parser[V] = $$$("[") ~>! repsep(toml_value, $$$(",")) <~ opt($$$(",")) ~ $$$("]")

    def table: Parser[T] = $$$("[") ~>! (keys <~ $$$("]")) ~! content ^?
      { case base ~ T(map) => to_map(List(base -> map)) }

    def inline_table: Parser[V] = $$$("{") ~>! (content ^? to_map) <~ $$$("}")

    def array_of_tables: Parser[T] =
      $$$("[[") ~>! (keys <~ $$$("]]")) >> { ks =>
        repsep(content ^^ to_map, $$$("[[") ~! (keys ^? { case ks1 if ks1 == ks => }) ~ $$$("]]")) ^^
          { list => List(ks -> list) } ^? to_map
      }

    def toml: Parser[T] = (content ~ rep(table | array_of_tables)) ^?
      { case T(map) ~ maps => map :: maps } ^? { case Merge(map) => map }


    /* auxiliary parsers */

    private def $$$(name: String): Parser[Token] = elem(name, _.is_keyword(name))

    private def token[A](name: String, p: Token => Boolean, parser: String => A): Parser[A] =
      elem(name, p) ^^ (tok => Try { parser(tok.text) }) ^? { case util.Success(v) => v }

    private def key: Parser[Key] = elem("key", e => e.is_ident || e.is_string) ^^ (_.text)

    private def toml_value: Parser[V] = string | integer | float | boolean | offset_date_time |
      local_date_time | local_date | local_time | array | inline_table

    private def content: Parser[List[(List[Key], V)]] = rep((keys <~ $$$("=")) ~! toml_value ^^
      { case ks ~ v => ks -> v })


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
                case x => return None
              }
              case None => k2 -> v2
            }
        }
        Some(map1.filter { case (k, _) => !map2.contains(k) } ++ res2)
      }

      def unapply(maps: List[T]): Option[T] = Some(maps.fold(Map.empty)(merge(_, _).getOrElse(return None)))
    }


    /* parse */

    def parse(input: CharSequence): T = {
      val scanner = new Lexer.Scanner(Scan.char_reader(input))
      val result = phrase(toml)(scanner)
      (result : @unchecked) match {
        case Success(toml, _) => toml
        case NoSuccess(_, next) => error("Malformed TOML input at " + next.pos)
      }
    }
  }

  object Parsers extends Parsers


  /* standard format */

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
