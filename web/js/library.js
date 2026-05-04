/* Author: Fabian Huch, TU Muenchen

Basic library.
 */

function try_unprefix(prfx, s) {
  if (s.startsWith(prfx)) return s.slice(prfx.length)
  else return null
}

function try_unsuffix(sffx, s) {
  if (s.endsWith(sffx)) return s.slice(0, -sffx.length)
  else return null
}

function perhaps_unprefix(prfx, s) { return try_unprefix(prfx, s) ?? s }
function perhaps_unsuffix(sffx, s) { return try_unsuffix(sffx, s) ?? s }

function parse_elem(html_str) {
  const template = document.createElement('template')
  template.innerHTML = html_str
  return template.content
}

function get_query(attribute) {
  const params = new URLSearchParams(window.location.search)
  return params.get(attribute)
}
