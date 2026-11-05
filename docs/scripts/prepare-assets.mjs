import { copyFileSync, mkdirSync } from 'node:fs'
import { fileURLToPath } from 'node:url'

const publicRoot = new URL('../public/', import.meta.url)
mkdirSync(publicRoot, { recursive: true })
for (const name of ['logo.png', 'logo-small.png']) {
  copyFileSync(
    fileURLToPath(new URL(`../../.github/assets/${name}`, import.meta.url)),
    fileURLToPath(new URL(name, publicRoot))
  )
}
