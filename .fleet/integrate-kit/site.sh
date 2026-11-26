#!/bin/bash
# usage: site.sh DIR OUT   (Blueprint Pages' build steps at DIR's checkout, autoform at the CI pin)
export PATH="$HOME/bin:$HOME/.elan/bin:$HOME/.local/bin:$PATH"
AF="git+https://github.com/facebookresearch/autoform-bot.git@46b46d6defaa19c618341e05c4cc0d819072a03d"
cd "$1" || exit 1
for d in site-src site; do test -e "$d" && mv "$d" "$d.old.$(date +%s)"; done
{
git rev-parse HEAD
uvx --from "$AF" autoform check blueprint; echo "CHECK-EXIT=$?"
uvx --from "$AF" autoform check blueprint --lean-root .; echo "CHECKLR-EXIT=$?"
uvx --from "$AF" autoform audit blueprint --lean-root .; echo "AUDIT-EXIT=$?"
uvx --from "$AF" autoform render blueprint --output site-src --lean-root . --require-declarations --ref "$(git rev-parse HEAD)"; echo "RENDER-EXIT=$?"
uvx --from mkdocs==1.6.1 --with mkdocs-material==9.7.7 --with mkdocs-literate-nav==0.6.2 --with markdown==3.10.3 --with pymdown-extensions==11.0.1 mkdocs build --strict; echo "MKDOCS-EXIT=$?"
uvx --from "$AF" autoform site check site --source site-src; echo "SITECHECK-EXIT=$?"
} > "$2" 2>&1
