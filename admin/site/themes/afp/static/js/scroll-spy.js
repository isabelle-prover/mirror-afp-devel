/**
 * Scrollspy, inspired from bootstrap. Original license:
 * --------------------------------------------------------------------------
 * Bootstrap (v5.1.3): scrollspy.js
 * Licensed under MIT (https://github.com/twbs/bootstrap/blob/main/LICENSE)
 *
 * --------------------------------------------------------------------------
 */

const EVENT_SPY_ACTIVATE = 'activate.spy'
const CLASS_ACTIVE = 'active'
const CLASS_SPY_LINK = 'spy-link'

/**
 * Class definition
 */

class ScrollSpy {
  constructor(element, target, target_suffix = "", offset = 0.5) {
    ScrollSpy.instance = this
    this._element = element

    this._offset = offset
    this._offsets = []
    this._link_ids = []
    this._active_id = null
    this._scrollHeight = 0
    this._target = target
    this._target_suffix = target_suffix

    window.onscroll = () => this._process()

    this.refresh()
    this._process()
  }

  refresh() {
    this._clear()
    this._offsets = []
    this._link_ids = []
    this._scrollHeight = this._get_scroll_height()

    const targets = []
    for (const link of document.getElementById(this._target).getElementsByClassName(CLASS_SPY_LINK)) {
      // visible and has id
      if (link.id && !is_collapsed(link)) {
        const target = document.getElementById(this._get_target_id(link))

        if (target) {
          const targetBCR = target.getBoundingClientRect()
          if (targetBCR.width || targetBCR.height) {
            targets.push([targetBCR.top + window.pageYOffset, link.id])
          }
        }
      }
    }

    for (const item of targets.sort((a, b) => a[0] - b[0])) {
      this._offsets.push(item[0])
      this._link_ids.push(item[1])
    }
  }

  // Private
  _get_target_id(link) {
    return link.getAttribute('href').slice(1) + this._target_suffix
  }
  
  _get_scroll_height() {
    return window.scrollHeight || Math.max(
      document.body.scrollHeight,
      document.documentElement.scrollHeight
    )
  }
  _process() {
    const scroll_top = window.pageYOffset + this._offset * window.innerHeight
    const scroll_height = this._get_scroll_height()
    const max_scroll = this._offset * window.innerHeight + scroll_height - window.innerHeight

    if (this._scrollHeight !== scroll_height) {
      this.refresh()
    }

    if (scroll_top >= max_scroll) {
      const target_id = this._link_ids[this._link_ids.length - 1]

      if (this._active_id !== target_id) {
        this._activate(target_id)
      }

      return
    }

    if (this._active_id && scroll_top < this._offsets[0] && this._offsets[0] > 0) {
      this._clear()
      return
    }

    for (let i = this._offsets.length; i--;) {
      const isActiveTarget = this._active_id !== this._link_ids[i] &&
        scroll_top >= this._offsets[i] &&
        (typeof this._offsets[i + 1] === 'undefined' || scroll_top < this._offsets[i + 1])

      if (isActiveTarget) {
        this._activate(this._link_ids[i])
      }
    }
  }

  _activate(link_id) {
    this._clear()
    this._active_id = link_id

    const link = document.getElementById(link_id)
    if (link) {
      const elem = document.getElementById(this._get_target_id(link))
      link.classList.add(CLASS_ACTIVE)
      elem.classList.add(CLASS_ACTIVE)

      const event = new Event(EVENT_SPY_ACTIVATE)
      event.relatedTarget = link
      window.dispatchEvent(event)
    }
  }

  _clear() {
    if (this._active_id) {
      const link = document.getElementById(this._active_id)
      if (link) {
        const elem = document.getElementById(this._get_target_id(link))
        if (link.classList.contains(CLASS_ACTIVE)) link.classList.remove(CLASS_ACTIVE)
        if (elem.classList.contains(CLASS_ACTIVE)) elem.classList.remove(CLASS_ACTIVE)
      }
    }
  }

  static instance
}