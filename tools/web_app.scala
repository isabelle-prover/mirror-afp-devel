/* Author: Fabian Huch, TU Muenchen

Technical layer for web apps using server-side rendering with HTML forms.
 */
package afp


import isabelle._

import scala.annotation.tailrec


object Web_App {
  val FILE = "file"
  val ACTION = "action"

  /* form html elements */

  object HTML {
    import isabelle.HTML._

    def css(s: String): Attribute = new Attribute("style", s)
    def name(n: String): Attribute = new Attribute("name", n)
    def value(v: String): Attribute = new Attribute("value", v)
    def placeholder(p: String): Attribute = new Attribute("placeholder", p)

    val italic = new Operator("i")
    val fieldset = new Operator("fieldset")
    val button = new Operator("button")

    def legend(txt: String): XML.Elem = XML.Elem(Markup("legend", Nil), text(txt))
    def input(typ: String): XML.Elem = XML.Elem(Markup("input", List("type" -> typ)), Nil)
    def hidden(k: String, v: String): XML.Elem = id(k)(name(k)(value(v)(input("hidden"))))

    def textfield(i: String, p: String, v: String): XML.Elem =
      id(i)(name(i)(value(v)(placeholder(p)(input("text")))))

    def browse(i: String, accept: List[String]): XML.Elem =
      id(i)(name(i)(input("file"))) + ("accept" -> accept.mkString(","))

    def label(`for`: String, txt: String): XML.Elem =
      XML.Elem(Markup("label", List("for" -> `for`)), text(txt))

    def fieldlabel(for_elem: String, txt: String): XML.Elem = label(for_elem, " " + txt + ": ")

    def explanation(for_elem: String, txt: String): XML.Elem =
      par(List(italic(List(label(for_elem, txt)))))

    def option(k: String, v: String): XML.Elem =
      XML.Elem(Markup("option", List("value" -> k)), text(v))

    def optgroup(txt: String, opts: XML.Body): XML.Elem =
      XML.Elem(Markup("optgroup", List("label" -> txt)), opts)

    def select(i: String, opts: XML.Body): XML.Elem =
      XML.Elem(Markup("select", List("id" -> i, "name" -> i)), opts)

    def textarea(i: String, v: String): XML.Elem =
      XML.Elem(Markup("textarea", List("id" -> i, "name" -> i, "value" -> v)), text(v + "\n"))

    def radio(i: String, v: String, values: List[(String, String)]): XML.Elem = {
      def to_option(k: String): XML.Elem = {
        val elem = id(i + k)(name(i)(value(k)(input("radio"))))
        if (v == k) elem + ("checked" -> "checked") else elem
      }

      div(values.flatMap { case (k, v) => List(label(i + k, v), to_option(k)) })
    }

    def selection(i: String, selected: Option[String], opts: XML.Body): XML.Elem = {
      def sel(elem: XML.Tree): XML.Tree = {
        selected match {
          case Some(value) =>
            val Value = new Properties.String("value")
            elem match {
              case XML.Elem(Markup("optgroup", props), body) =>
                XML.Elem(Markup("optgroup", props), body.map(sel))
              case e@XML.Elem(Markup("option", Value(v)), _) if v == value =>
                e + ("selected" -> "selected")
              case e => e
            }
          case None => elem
        }
      }

      def is_empty_group(elem: XML.Tree): Boolean = elem match {
        case XML.Elem(Markup("optgroup", _), body) if body.isEmpty => true
        case _ => false
      }

      val default = if (selected.isEmpty) List(option("", "") + ("hidden" -> "hidden")) else Nil
      select(i, default ::: opts.filterNot(is_empty_group).map(sel))
    }

    def api_button(call: String, label: String): XML.Elem =
      button(text(label)) + ("formaction" -> call) + ("type" -> "submit")

    def action_button(call: String, label: String, action: String): XML.Elem =
      name(ACTION)(value(action)(api_button(call, label)))

    def submit_form(endpoint: String, body: XML.Body): XML.Elem = {
      val default_button = css("display: none")(input("submit") + ("formaction" -> endpoint))
      val attrs =
        List("method" -> "post", "target" -> "iframe", "enctype" -> "multipart/form-data")
      XML.Elem(Markup("form", attrs), default_button :: body)
    }
  }


  /* request parameters */

  object Params {
    type Key = String
    val empty: Key = ""

    object Nest_Key {
      def apply(k: Key, field: String): Key =
        if (k == empty) field else k + "_" + field

      def unapply(k: Key): Option[(Key, String)] =
        k.split('_').filterNot(_.isEmpty).toList.reverse match {
          case k :: ks => Some(ks.reverse.mkString("_"), k)
          case _ => None
        }
    }

    object List_Key {
      def apply(k: Key, field: String, i: Int): Key =
        Nest_Key(k, field + "_" + i.toString)

      def unapply(k: Key): Option[(Key, (String, Int))] =
        k.split('_').filterNot(_.isEmpty).toList.reverse match {
          case Value.Int(i) :: k :: ks => Some(ks.reverse.mkString("_"), (k, i))
          case _ => None
        }

      def num(field: String, k: Key): Option[Int] = k match {
        case List_Key(_, (f, i)) if f == field => Some(i)
        case _ => None
      }

      def split(field: String, k: Key): Option[(Key, Int)] = k match {
        case List_Key(key, (f, i)) if f == field => Some(key, i)
        case _ => None
      }
    }


    /* strucutred data */

    class Data private[Params](
      v: Option[String] = None,
      elem: Map[String, Data] = Map.empty,
      elems: Map[String, List[Data]] = Map.empty
    ) {
      def is_empty: Boolean = v.isEmpty && elem.isEmpty && elems.isEmpty

      override def toString: String = {
        val parts = v.map(quote).toList ++
          elem.toList.map { case (k, v) => k + " -> " + v.toString } ++
          elems.toList.map { case (k, v) => k + " -> (" + v.mkString + ")" }
        "{" + parts.mkString(", ") + "}"
      }

      def value: String = v.getOrElse("")

      def get(field: String): Data = elem.getOrElse(field, new Data())

      def list(field: String): List[Data] = elems.getOrElse(field, Nil)
    }

    object Data {
      def from_multipart(parts: List[Multi_Part.Data]): Data = {
        sealed trait E
        case class Value(rep: String) extends E
        case class Index(i: Int, to: E) extends E
        case class Nest(field: String, to: E) extends E

        def group_map[A, B, C](v: List[(C, A)], agg: List[A] => B): Map[C, B] =
          v.groupBy(_._1).view.mapValues(_.map(_._2)).mapValues(agg).toMap

        def to_list(l: List[(Int, E)]): List[Data] = {
          val t: List[(Int, Data)] = group_map(l, parse).toList
          t.sortBy(_._1).map(_._2)
        }

        def parse(e: List[E]): Data = {
          val value = e.collectFirst { case Value(rep) => rep }
          val nest_by_key = e.collect {
            case Nest(field, v: Value) => field -> v
            case Nest(field, v: Nest) => field -> v
          }
          val elem = group_map(nest_by_key, parse)
          val list_by_key = e.collect {
            case Nest(field, Index(i, to)) => field -> (i -> to)
          }
          val elems = group_map(list_by_key, to_list)

          new Data(value, elem, elems)
        }

        @tailrec
        def expand(key: Key, to: E): E = key match {
          case List_Key(key, (field, i)) => expand(key, Nest(field, Index(i, to)))
          case Nest_Key(key, field) => expand(key, Nest(field, to))
          case _ => to
        }

        val params =
          parts.flatMap {
            case Multi_Part.Param(name, value) => List(name -> value)
            case Multi_Part.File(name, file_name, content) =>
              List(name -> file_name, Nest_Key(name, Web_App.FILE) -> content.encode_base64)
          }
        parse(params.map { case (k, v) => expand(k, Value(v)) })
      }
    }
  }


  /* form http handling */

  object Multi_Part {
    abstract class Data(name: String)
    case class Param(name: String, value: String) extends Data(name)
    case class File(name: String, file_name: String, content: Bytes) extends Data(name)

    def parse(body: Bytes): List[Data] = {
      /* Seq for text with embedded bytes */
      case class Seq(text: String, bytes: Bytes) {
        def split_one(sep: String): Option[(Seq, Seq)] = {
          val text_i = text.indexOf(sep)
          if (text_i >= 0 && sep.nonEmpty) {
            val (before_text, at_text) = text.splitAt(text_i)
            val after_text = at_text.substring(sep.length)

            var bytes_i = 0
            var res = ""
            var it: Iterator[Byte] = bytes.iterator
            while (res != sep && it.hasNext) {
              val (trash, rest) = it.span(_.toChar != sep.head)
              it = rest
              bytes_i += trash.length
              val it2 = sep.iterator
              val (res2, rest2) = it.span(t => it2.hasNext && it2.next() == t.toChar)
              it = rest2
              res = res2.map(_.toChar).mkString
              bytes_i += res.length
            }

            val before_bytes = bytes.subSequence(0, bytes_i - sep.length)
            val after_bytes = bytes.subSequence(bytes_i, bytes.length)

            Some(Seq(before_text, before_bytes), Seq(after_text, after_bytes))
          } else None
        }
      }

      val s = Seq(body.text, body)

      def perhaps_unprefix(pfx: String, s: Seq): Seq = {
        Library.try_unprefix(pfx, s.text) match {
          case Some(text) => Seq(text, s.bytes.subSequence(pfx.length, s.bytes.length))
          case None => s
        }
      }

      val Separator = """--(.*)""".r

      s.split_one(HTTP.NEWLINE) match {
        case Some(Seq(Separator(sep), _), rest) =>
          val Param = """Content-Disposition: form-data; name="([^"]+)"""".r
          val File = """Content-Disposition: form-data; name="([^"]+)"; filename="([^"]+)"""".r

          def parts(body: Seq): Option[List[Data]] =
            for {
              (first_line, more) <- body.split_one(HTTP.NEWLINE)
              more1 = perhaps_unprefix(HTTP.NEWLINE, more)
              (value, rest) <- more1.split_one(HTTP.NEWLINE + "--" + sep)
              rest1 = perhaps_unprefix(HTTP.NEWLINE, rest)
            } yield first_line.text match {
              case Param(name) =>
                Multi_Part.Param(name, Line.normalize(value.text)) :: parts(rest1).getOrElse(Nil)
              case File(name, file_name) =>
                value.split_one(HTTP.NEWLINE + HTTP.NEWLINE) match {
                  case Some(_, content) =>
                    Multi_Part.File(name, file_name, content.bytes) :: parts(rest1).getOrElse(Nil)
                  case _ => parts(rest1).getOrElse(Nil)
                }
              case _ => Nil
            }

          parts(rest).getOrElse(Nil)
        case _ => Nil
      }
    }
  }

  abstract class Server[A](
    port: Int = 0,
    verbose: Boolean = false,
    progress: Progress = new Progress()
  ) {
    def render(model: A): XML.Body
    val error: A
    val endpoints: List[Endpoint]

    def output(body: XML.Body): String = {
      "<!DOCTYPE html><body onLoad='parent.postMessage(document.body.scrollHeight, \"*\")'>" +
        isabelle.HTML.output(body, hidden = true, structural = true) +
        "</body>"
    }

    abstract class Endpoint(path: String, method: String = "GET")
      extends HTTP.Service(path.stripPrefix("/"), method)

    class Get(path: String, description: String, model: A)
      extends Endpoint(path) {

      def apply(request: HTTP.Request): Option[HTTP.Response] = {
        progress.echo_if(verbose, "GET " + description)
        Some(HTTP.Response.html(output(render(model))))
      }
    }

    class Post(path: String, description: String, update: Params.Data => Option[A])
      extends Endpoint(path, method = "POST") {

      def apply(request: HTTP.Request): Option[HTTP.Response] = {
        progress.echo_if(verbose, "POST " + description)

        val parts = Multi_Part.parse(request.input)
        val params = Params.Data.from_multipart(parts)
        progress.echo_if(verbose, params.toString)

        val model = update(params).getOrElse(error)
        Some(HTTP.Response.html(output(render(model))))
      }
    }

    private lazy val server = HTTP.server(port = port, name = "", services = endpoints)

    def run(): Unit = {
      start()

      @tailrec
      def loop(): Unit = {
        Thread.sleep(Long.MaxValue)
        loop()
      }

      Isabelle_Thread.interrupt_handler(_ => server.stop()) { loop() }
    }

    def start(): Unit = {
      server.start()
      progress.echo("Server started on port " + server.http_server.getAddress.getPort)
    }

    def stop(): Unit = {
      server.stop()
      progress.echo("Server stopped")
    }
  }
}