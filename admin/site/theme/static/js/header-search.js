function load_search(input, keywords) {
  const suggest_index = get_suggest_index(keywords)

  input.addEventListener("keyup", function (event) {
    switch (event.key) {
      case "Enter":
      case "Up":
      case "ArrowUp":
      case "Down":
      case "ArrowDown":
      case "Left":
      case "ArrowLeft":
      case "Right":
      case "ArrowRight":
      case "Escape":
        break
      default:
        if (this.value && this.value.length > 1) {
          add_suggestions(suggest_index, this.value)
        }
    }
  })

  input.addEventListener("keydown", function (event) {
    switch (event.key) {
      case "Enter":
        event.preventDefault() // prevent the form from being submitted
        handle_submit(this.value)
        break
      default:
    }
  })

  input.addEventListener("change", function () {
    handle_submit(this.value)
  })
}

function handle_submit(value) {
  if (typeof history.pushState !== "undefined") {
    document.location = window.location.origin + "/search/?s=" + value
  }
}

document.addEventListener("DOMContentLoaded", function () {
  const input = document.getElementById("search-input")
  const button = document.getElementById("search-button")
  if (button) {
    button.addEventListener("click", () => {
      handle_submit(input.value)
    })
  }

  Promise.all([fetch("/data/keywords.json")])
    .then(function (responses) {
      // Get a JSON object from each of the responses
      return Promise.all(responses.map((response) => response.json()))
    })
    .then((data) => load_search(input, ...data))
})
