/* Author: Fabian Huch, TU Muenchen

Dynamic loading of HTML presentation for theories.
 */

const BROWSER_INFO = '/browser_info/current/'
const CLASS_LOADER = 'loader'
const CLASS_ANIMATION = 'animation'
const ID_THEORY = 'theory'


/* redirect hrefs */

function target(base, href) {
  const url = new URL(href, base)
  if (!url.pathname.startsWith(BROWSER_INFO)) return url.href
  else {
    const path = perhaps_unsuffix(".html", perhaps_unprefix(BROWSER_INFO, url.pathname))

    const name_parts = path.split('/')
    if (name_parts.length !== 3) return url.href
    else {
      const [chapter, session, theory] = name_parts
      const theory_parts = theory.split('.')

      function thy_href(session, theory) {
        const path = '../' + session + '/' + theory + '.html'
        if (url.hash === '') return path
        else return path + url.hash
      }

      if (theory_parts.length === 1) return thy_href(session, theory)
      else return url.href
    }
  }
}


/* theory lazy-loading */

async function fetch_theory(href) {
  const html_str = await fetch(href).then((http_res) => {
    if (http_res.status !== 200)
      return Promise.resolve(
        `<body><pre>Could not load theory: ${http_res.statusText}</pre></body>`)
    else return http_res.text()
  }).catch((_) => {
    console.log(`Could not load theory at '${href}'. Redirecting...`)
    window.location.replace(href)
  })

  const parser = new DOMParser()
  const html = parser.parseFromString(html_str, 'text/html')
  return html.getElementsByTagName('body')[0]
}

const load_theory = async () => {
  const thy_elem = document.getElementById(ID_THEORY)

  if (thy_elem) {
    const thy_href = thy_elem.getAttribute("href")
    const spinner =
      parse_elem(
        `<div id="spinner" class=${CLASS_LOADER}><div class=${CLASS_ANIMATION}></div></div>`)
    thy_elem.replaceWith(spinner)

    const thy_body = await fetch_theory(thy_href)
    for (const link of thy_body.getElementsByTagName('a')) {
      const rel_href = link.getAttribute('href')
      link.setAttribute('href', target(thy_href, rel_href))
    }

    const thy_pre = Array(...thy_body.getElementsByTagName("pre"))[0]
    document.getElementById("spinner").replaceWith(thy_pre)
    const id = location.hash.slice(1)
    if (id) document.getElementById(id)?.scrollIntoView()
  }
}

document.addEventListener('DOMContentLoaded', load_theory)
