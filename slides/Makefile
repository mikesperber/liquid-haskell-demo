SOURCES = $(wildcard *.org)
HTML = $(SOURCES:.org=.html)
PDF = $(SOURCES:.org=.pdf)
CHROME = $(shell which google-chrome-beta || which google-chrome-stable || which google-chrome || which chromium || echo "`pwd`/mac-chrome.sh")
MAYBE_CHROME_PATH = $(if $(CHROME),--chrome-path $(CHROME),)
RESOURCES = $(shell find css -type f)

ONEPDF=all-slides.pdf

all: $(HTML)
.PHONY: all

flake.lock: flake.nix
	nix flake lock

# If the lockfile changes, slides need to be rebuilt
%.html: %.org flake.lock
	nix run .# -- "$<"

# Use a specific window size to work around this issue:
# https://github.com/astefanutti/decktape/issues/151
%.pdf: %.html $(RESOURCES)
	nix build .#decktapeWithDependencies -o result-decktape
	nix run .#decktape -- -s 2048x1536 $(MAYBE_CHROME_PATH) "$<" "$@"

pdf: $(PDF)
.PHONY: pdf

one-pdf: $(ONEPDF)
.PHONY: one-pdf

$(ONEPDF): $(PDF)
	nix run .#pdfunite -- $(PDF) $(ZIPPREFIX).pdf

clean:
	rm -f $(HTML) $(PDF) $(ONEPDF)
.PHONY: clean
