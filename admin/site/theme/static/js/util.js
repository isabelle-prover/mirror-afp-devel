
/* utilities */

function strip_prefix(str, prefix) {
  if (str.startsWith(prefix)) return str.slice(prefix.length)
  else return str
}

function parse_elem(html_str) {
  const template = document.createElement('template')
  template.innerHTML = html_str
  return template.content
}

function get_query(attribute) {
  const params = new URLSearchParams(window.location.search)
  return params.get(attribute)
}
