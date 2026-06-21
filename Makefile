# SPDX-License-Identifier: AGPL-3.0-only
AGDA   ?= agda
PANDOC ?= pandoc
EVERYTHING := src/Everything.lagda.md
HTML_DIR   := _build/html
SITE_DIR   := _build/site

.PHONY: typecheck html site clean

# Type-check the whole development.
typecheck:
	$(AGDA) $(EVERYTHING)

# Run Agda's built-in HTML backend: literate (.lagda.md) modules become
# highlighted, cross-linked .md; plain .agda dependencies become .html.
html:
	$(AGDA) --html --html-highlight=auto --html-dir=$(HTML_DIR) $(EVERYTHING)

# Turn Agda's output into a browsable site: pandoc renders each .md to .html
# (keeping the highlighted <pre class="Agda"> blocks and their cross-references),
# the already-.html dependency pages and the CSS are copied over, and a landing
# page redirects to the umbrella module.
site: html
	rm -rf $(SITE_DIR)
	mkdir -p $(SITE_DIR)
	cp $(HTML_DIR)/*.css  $(SITE_DIR)/ 2>/dev/null || true
	cp $(HTML_DIR)/*.html $(SITE_DIR)/ 2>/dev/null || true
	for f in $(HTML_DIR)/*.md; do \
	  base=$$(basename "$$f" .md); \
	  $(PANDOC) --standalone --metadata title="$$base" --css Agda.css "$$f" -o "$(SITE_DIR)/$$base.html"; \
	done
	printf '<!doctype html>\n<meta charset="utf-8">\n<title>QIITOrd</title>\n<meta http-equiv="refresh" content="0; url=QIITOrd.html">\n<p><a href="QIITOrd.html">QIITOrd documentation</a></p>\n' > $(SITE_DIR)/index.html
	touch $(SITE_DIR)/.nojekyll
	@echo "Site built in $(SITE_DIR)"

clean:
	rm -rf _build
