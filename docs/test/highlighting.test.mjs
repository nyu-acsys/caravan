import assert from 'node:assert/strict'
import { readFileSync } from 'node:fs'
import test from 'node:test'
import { createMarkdownRenderer } from 'vitepress'
import { defineProjectSite } from '@nyu-acsys/docs-kit/config'
import project from '../.vitepress/project.mjs'

const config = defineProjectSite(project, { markdown: { languages: ['ocaml'] } })
const renderer = await createMarkdownRenderer(project.root, config.markdown, '/')
const render = (code, language = 'proof') => renderer.render(`\`\`\`${language}\n${code}\n\`\`\``)

function styleOf(html, word) {
  const match = html.match(new RegExp(`<span style="([^"]+)">\\s*${word}\\s*</span>`))
  assert.ok(match, `Missing highlighted token: ${word}`)
  return match[1]
}

test('proof keywords retain Caravan highlighting after OCaml declarations and inside scopes', () => {
  for (const [file, keywords] of [
    ['automatic_cell.proof', ['invariant', 'view', 'action', 'linearizes', 'proof', 'initially', 'performs']],
    ['manual_cell.proof', ['module', 'struct', 'let', 'proof', 'fun', 'unfold', 'fold']]
  ]) {
    const code = readFileSync(new URL(`../examples/${file}`, import.meta.url), 'utf8')
    for (const language of ['proof', 'caravan-proof']) {
      const html = render(code, language)
      for (const keyword of keywords) {
        assert.equal(styleOf(html, keyword), styleOf(render(keyword), keyword), `${file}: ${keyword}`)
      }
    }
  }
})

test('proof keywords inside comments and strings retain their literal highlighting', () => {
  const html = render('type state = { value : int }\n(* requires *)\nlet text = "requires"')
  const keywordStyle = styleOf(render('requires'), 'requires')
  assert.ok(!html.includes(`<span style="${keywordStyle}">requires</span>`))
  assert.ok(html.includes('(* requires *)'))
  assert.ok(html.includes(' "requires"</span>'))
})
