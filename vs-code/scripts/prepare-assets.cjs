const fs = require('node:fs');
const path = require('node:path');

const extension = path.resolve(__dirname, '..');
fs.mkdirSync(path.join(extension, 'images'), { recursive: true });
fs.copyFileSync(
  path.join(extension, '..', '.github', 'assets', 'logo-icon.png'),
  path.join(extension, 'images', 'icon.png')
);
