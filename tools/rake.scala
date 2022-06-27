/* Author: Fabian Huch, TU Muenchen

Rapid keyword extraction algorithm. From:
Rose, S., Engel, D., Cramer, N., & Cowley, W. (2010). Automatic keyword extraction from individual
documents. Text mining: applications and theory, 1(1-20), 10-1002.
 */
package afp


import isabelle._

import scala.util.matching.Regex

import java.io.{BufferedReader, InputStreamReader}


object Rake {
  private val max_words = 2
  private val min_chars = 3

  private val number = "^[0-9]+$".r
  private val replacements = List(
    "<[^>]*>".r -> "",
    "[^\\w\\s()'.,;:-]".r -> " ",
    "\\s+".r -> " ")

  private lazy val stop_words: Regex = {
    val stream = getClass.getClassLoader.getResourceAsStream("SmartStoplist.txt")
    val reader = new BufferedReader(new InputStreamReader(stream))
    val stop_words = File.read_lines(reader, _ => ()).filterNot(_.startsWith("#")).map(_.strip)
    val regex = "\\b(?i)(" + stop_words.map(l => l + "(?![\\w-])").mkString("|") + ")"
    regex.r
  }

  val sentence_delimiters = "[.!?,;:\t\\\\\"()'\u2019\u2013]|\\s-\\s".r
  val word_delimiters = "[^a-zA-Z0-9_+-/]".r

  def separate_words(text: String): List[String] = {
    for {
      word_raw <- word_delimiters.split(text).toList
      word = word_raw.strip.toLowerCase
      if word.nonEmpty && word.length >= min_chars && !number.matches(word)
    } yield word
  }

  def calculate_word_scores(phrases: List[String]): Map[String, Double] = {
    def count(words: List[String], freq: Int, deg: Int): Option[(Int, Int)] =
      Some((freq + 1, deg + words.length - 1))

    var counts = Map.empty[String, (Int, Int)]
    for {
      phrase <- phrases
      words = separate_words(phrase)
      word <- words
    } counts = counts.updatedWith(word) {
      case Some((freq, deg)) => count(words, freq, deg)
      case None => count(words, 0, 0)
    }
    counts.view.mapValues { case (freq, deg) => (deg + freq).toDouble / freq }.toMap
  }

  def extract_keywords(text: String): List[(String, Double)] = {
    val stripped_text = replacements.foldLeft(text) {
      case (res, (regex, replacement)) => regex.replaceAllIn(res, replacement)
    }

    val phrases = for {
      sentence <- sentence_delimiters.split(stripped_text)
      phrase <- stop_words.split(sentence)
      if !phrase.isBlank
    } yield phrase.strip().toLowerCase

    val word_scores = calculate_word_scores(phrases.toList)

    val keywords = phrases.filter(_.split(' ').length <= max_words).map(phrase =>
      phrase -> separate_words(phrase).map(word_scores.getOrElse(_, 0.0)).sum)

    keywords.sortBy(_._2).toList.reverse
  }
}