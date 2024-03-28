/* Author: Fabian Huch, TU Muenchen

Technical layer for web apps using server-side rendering with HTML forms.
 */
package afp


import isabelle.*

import scala.annotation.tailrec


object Web_App {
  val FILE = "file"
  val ACTION = "action"

  /* form html elements */

  object More_HTML {
    import HTML._

    def css(s: String): Attribute = new Attribute("style", s)
    def name(n: String): Attribute = new Attribute("name", n)
    def value(v: String): Attribute = new Attribute("value", v)
    def placeholder(p: String): Attribute = new Attribute("placeholder", p)

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
      par(List(emph(List(label(for_elem, txt)))))

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

      span(values.map { case (k, v) => span(List(label(i + k, v), to_option(k))) })
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


    /* structured data */

    class Data private[Params](
      v: Option[String] = None,
      elem: Map[String, Data] = Map.empty,
      elems: Map[String, List[Data]] = Map.empty
    ) {
      def is_empty: Boolean = v.isEmpty && elem.isEmpty && elems.isEmpty

      override def toString: String = {
        val parts =
          v.map(v => if (v.length <= 100) quote(v) else quote(v.take(100) + "...")).toList ++
          elem.toList.map { case (k, v) => k + " -> " + v.toString } ++
          elems.toList.map { case (k, v) => k + " -> (" + v.mkString(",") + ")" }
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
        def expand(key: Key, to: E): E =
          key match {
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

            // text might be shorter than bytes because of misinterpreted characters
            var found = false
            var bytes_i = 0
            while (!found && bytes_i < bytes.length) {
              var sep_ok = true
              var sep_i = 0
              while (sep_ok && sep_i < sep.length) {
                if (bytes.charAt(bytes_i + sep_i) == sep.charAt(sep_i)) {
                  sep_i += 1
                } else {
                  bytes_i += 1
                  sep_ok = false
                }
              }
              if (sep_ok) found = true
            }

            val before_bytes = bytes.subSequence(0, bytes_i)
            val after_bytes = bytes.subSequence(bytes_i + sep.length, bytes.length)

            Some(Seq(before_text, before_bytes), Seq(after_text, after_bytes))
          } else None
        }
      }

      val s = Seq(body.text, body)

      def perhaps_unprefix(pfx: String, s: Seq): Seq =
        Library.try_unprefix(pfx, s.text) match {
          case Some(text) => Seq(text, s.bytes.subSequence(pfx.length, s.bytes.length))
          case None => s
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


  /* API with backend base path, and application url (e.g. for frontend links). */

  class API(val app: Url, val base_path: Path, val devel: Boolean = false) {
    def url(path: Path, params: Properties.T = Nil): String = {
      def param(p: Properties.Entry): String = Url.encode(p._1) + "=" + Url.encode(p._2)
      if (params.isEmpty) path.implode else path.implode + "?" + params.map(param).mkString("&")
    }

    def api_path(path: Path, external: Boolean = true): Path =
      (if (devel) Path.explode("backend") else Path.current) +
        (if (external) base_path else Path.current) + path

    def api_url(path: Path, params: Properties.T = Nil, external: Boolean = true): String =
      "/" + url(api_path(path, external = external), params)

    def app_url(path: Path, params: Properties.T = Nil): String =
      app.toString + "/" + url(path, params)
  }

  abstract class Server[A](
    api: API,
    port: Int = 0,
    verbose: Boolean = false,
    progress: Progress = new Progress()
  ) {
    def render(model: A): XML.Body
    val error_model: A
    val endpoints: List[Endpoint]
    val head: XML.Body

    def output_document(content: XML.Body, post_height: Boolean = true): String = {
      val attrs =
        if (post_height) List("onLoad" -> "parent.postMessage(document.body.scrollHeight, '*')")
        else Nil

      cat_lines(
        List(
          HTML.header,
          HTML.output(XML.elem("head", HTML.head_meta :: head), hidden = true, structural = true),
          HTML.output(XML.Elem(Markup("body", attrs), content), hidden = true, structural = true),
          HTML.footer))
    }

    class UI(path: Path) extends HTTP.Service(path.implode, "GET") {
      def apply(request: HTTP.Request): Option[HTTP.Response] = {
        progress.echo_if(verbose, "GET ui")

        val on_load = """
(function() {
  window.addEventListener('message', (event) => {
    if (Number.isInteger(event.data)) {
      this.style.height=event.data + 32 + 'px'
    }
  })
}).call(this)"""

        val set_src = """
const base = '""" + api.app.toString.replace("/", "\\/") + """'
document.getElementById('iframe').src = base + '""" + api.api_url(path).replace("/", "\\/") + """' + window.location.search"""

        Some(HTTP.Response.html(output_document(
          List(
            XML.Elem(
              Markup(
                "iframe",
                List(
                  "id" -> "iframe",
                  "name" -> "iframe",
                  "style" -> "border-style: none; width: 100%",
                  "onload" -> on_load)),
              HTML.text("content")),
            HTML.script(set_src)),
            post_height = false)))
      }
    }

    sealed abstract class Endpoint(path: Path, method: String = "GET")
      extends HTTP.Service(api.api_path(path, external = false).implode, method) {

      def reply(request: HTTP.Request): HTTP.Response

      final def apply(request: HTTP.Request): Option[HTTP.Response] =
        Exn.capture(reply(request)) match {
          case Exn.Res(res) => Some(res)
          case Exn.Exn(exn) =>
            val id = UUID.random_string()
            progress.echo_error_message("Internal error <" + id + ">: " + exn)
            error("Internal server error. ID: " + id)
        }
    }

    private def query_params(request: HTTP.Request): Properties.T = {
      def decode(s: String): Option[Properties.Entry] =
        s match {
          case Properties.Eq(k, v) => Some(Url.decode(k) -> Url.decode(v))
          case _ => None
        }

      Library.try_unprefix(request.query, request.uri_name).toList.flatMap(params =>
        space_explode('&', params).flatMap(decode))
    }


    /* endpoint types */

    class Get(val path: Path, description: String, get: Properties.T => Option[A])
      extends Endpoint(path) {

      def reply(request: HTTP.Request): HTTP.Response = {
        progress.echo_if(verbose, "GET " + description)

        val params = query_params(request)
        progress.echo_if(verbose, "params: " + params.toString())

        val model =
          get(params) match {
            case Some(model) => model
            case None =>
              progress.echo_if(verbose, "Parsing failed")
              error_model
          }
        HTTP.Response.html(output_document(render(model)))
      }
    }

    class Get_File(path: Path, description: String, download: Properties.T => Option[Path])
      extends Endpoint(path) {

      def reply(request: HTTP.Request): HTTP.Response = {
        progress.echo_if(verbose, "DOWNLOAD " + description)

        val params = query_params(request)
        progress.echo_if(verbose, "params: " + params.toString())

        download(params) match {
          case Some(path) => HTTP.Response.content(HTTP.Content.read(path))
          case None =>
            progress.echo_if(verbose, "Fetching file path failed")
            HTTP.Response.html(output_document(render(error_model)))
        }
      }
    }

    class Post(path: Path, description: String, post: Params.Data => Option[A])
      extends Endpoint(path, method = "POST") {

      def reply(request: HTTP.Request): HTTP.Response = {
        progress.echo_if(verbose, "POST " + description)

        val parts = Multi_Part.parse(request.input)
        val params = Params.Data.from_multipart(parts)
        progress.echo_if(verbose, "params: " + params.toString)

        val model =
          post(params) match {
            case Some(model) => model
            case None =>
              progress.echo_if(verbose, "Parsing failed")
              error_model
          }
        HTTP.Response.html(output_document(render(model)))
      }
    }


    /* server */

    private lazy val services =
      endpoints ::: (if (api.devel) endpoints.collect { case g: Get => new UI(g.path) } else Nil)
    private lazy val server = HTTP.server(port = port, name = "", services = services)

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