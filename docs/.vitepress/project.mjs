import { fileURLToPath } from 'node:url'
import { createSections } from '@nyu-acsys/docs-kit/sections'

const root = fileURLToPath(new URL('../', import.meta.url))

export const tutorialChapters = [
  { path: 'tutorial/', label: '1', title: 'Getting started' },
  { path: 'tutorial/contracts', label: '2', title: 'Contracts and ownership' },
  { path: 'tutorial/concurrent-proofs', label: '3', title: 'Concurrent proofs' },
  { path: 'tutorial/ocaml-subset', label: '4', title: 'OCaml coverage' },
  { path: 'tutorial/semantics', label: '5', title: 'Semantics and verification limits' }
]

export default {
  root,
  sections: createSections({ root, chapters: tutorialChapters }),
  pagesBase: '/caravan/',
  sourceExtensions: ['ml', 'mli', 'proof'],
  exampleSources: ['examples'],
  grammars: [
    { file: new URL('../../vs-code/syntaxes/spec.tmLanguage.json', import.meta.url), aliases: ['caravan-spec'] },
    { file: new URL('../../vs-code/syntaxes/ocaml-injection.tmLanguage.json', import.meta.url), aliases: ['caravan-annotation'] },
    { file: new URL('../../vs-code/syntaxes/proof.tmLanguage.json', import.meta.url), aliases: ['proof', 'caravan-proof'] },
    { file: new URL('./caravan.tmLanguage.json', import.meta.url), aliases: ['caravan', 'caravan-ocaml'] }
  ]
}
