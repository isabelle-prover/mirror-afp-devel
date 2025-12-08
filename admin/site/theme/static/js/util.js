
/* utilities */

const strip_prefix = (str, prefix) => {
  if (str.startsWith(prefix)) return str.slice(prefix.length)
  else return str
}

const parse_elem = (html_str) => {
  const template = document.createElement('template')
  template.innerHTML = html_str
  return template.content
}

const escape_html = (html) => {
  return html.replace(/[&<>"']/g, function(m) {
    switch (m) {
      case '&':
        return '&amp;'
      case '<':
        return '&lt;'
      case '>':
        return '&gt;'
      case '"':
        return '&quot;'
      case "'":
        return '&#39;'
    }
  })
}

function get_query(attribute) {
  const params = new URLSearchParams(window.location.search)
  return params.get(attribute)
}

function memoize(fun) {
  const cache = {}
  return function (n) {
    if (cache[n] !== undefined) {
      return cache[n]
    } else {
      let result = fun(...n)
      cache[n] = result
      return result
    }
  }
}
