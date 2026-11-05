import { fileURLToPath } from 'node:url'

export default {
  root: fileURLToPath(new URL('../', import.meta.url)),
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
