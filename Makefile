# Options added to the autogenerated `everything.lagda.md` file.
# We put options that apply to all files into the `agda-unimath.agda-lib` file,
# but there are some options that we want to enable only for specific source
# files, and if these options are pervasive (i.e. they need to be enabled in all
# modules that include the modules that have them enabled), then they need to be
# added to the everything file as well.
everythingOpts := --guardedness --cohesion --flat-split --rewriting
# use "$ export AGDAVERBOSE=-v20" if you want to see all
AGDAVERBOSE ?= -v1

ifeq ($(CI),)
	AGDA_MIN_HEAP ?= 2G
else
	AGDA_MIN_HEAP ?= 4G
endif

AGDARTS := +RTS -H$(AGDA_MIN_HEAP) -M6G -RTS
AGDAFILES := $(shell find src -name temp -prune -o -type f \( -name "*.lagda.md" -not -name "everything.lagda.md" \) -print)
CONTRIBUTORS_FILE := CONTRIBUTORS.toml

# All our code is in literate Agda, so we could set highlight=code and drop the
# css flag, which only affects how files with the .agda extension are processed.
# However, the HTML backend also processes referenced library files
# (Agda.Primitive at the time of writing), which is a pure Agda file, and
# setting higlight=code would make it not recognized as code at all, so the
# resulting page looks garbled. With highlight=auto and the default Agda.css, it
# at is at least in a proper code block with syntax highlighting, albeit without
# the agda-unimath chrome.
AGDAHTMLFLAGS ?= --html --html-highlight=auto --html-dir=docs --css=website/css/Agda.css --only-scope-checking
AGDAPROFILEFLAGS ?= --profile=modules +RTS -s -RTS
AGDA ?= agda $(AGDAVERBOSE) $(AGDARTS)
TIME ?= time

METAFILES := \
	ART.md \
	CITE-THIS-LIBRARY.md \
	CITING-SOURCES.md \
	CODINGSTYLE.md \
	CONTRIBUTING.md \
	CONTRIBUTORS.md \
	FILE-CONVENTIONS.md \
	DESIGN-PRINCIPLES.md \
	GRANT-ACKNOWLEDGEMENTS.md \
	HOME.md \
	HOWTO-INSTALL.md \
	LICENSE.md \
	MIXFIX-OPERATORS.md \
	MAINTAINERS.md \
	README.md \
	STATEMENT-OF-INCLUSION.md \
	SUMMARY.md \
	TEMPLATE.lagda.md \
	PROJECTS.md \
	VISUALIZATION.md

.PHONY: agdaFiles
agdaFiles:
	@rm -rf $@
	@rm -rf ./src/everything.lagda.md
	@git ls-files src | grep '\.lagda.md$$' > $@
	@sort -o $@ $@
	@wc -l $@
	@echo "$(shell (git ls-files src | grep '.lagda.md$$' | xargs cat) | wc -l) LOC"

.PHONY: ./src/everything.lagda.md
src/everything.lagda.md: agdaFiles
	@echo "\`\`\`agda" > $@ ;\
	echo "{-# OPTIONS $(everythingOpts) #-}" >> $@ ;\
	echo "" >> $@ ;\
	echo "module everything where" >> $@ ;\
	cat agdaFiles \
		| cut -c 5-               \
		| cut -f1 -d'.'           \
		| sed 's/\//\./g'         \
		| awk 'BEGIN { FS = "."; OFS = "."; lastdir = "" } { if ($$1 != lastdir) { print ""; lastdir = $$1 } print "open import " $$0 " public"}' \
		>> $@ ;\
	echo "\`\`\`" >> $@ ;

.PHONY: check
check: ./src/everything.lagda.md
	${TIME} ${AGDA} $?

.PHONY: check-profile
# `clean` is specified second so that the $< variable stores the everything file.
# We don't mind, because the `clean` target busts the typechecking and website cache,
# but doesn't touch the everything file.
check-profile: ./src/everything.lagda.md clean
	${AGDA} ${AGDAPROFILEFLAGS} $<

# Base directory where Agda interface files are stored
BUILD_DIR := ./_build
# Directory for temporary files
TEMP_DIR := ./temp
# Convert module path to directory path (replace dots with slashes)
MODULE_DIR = $(subst .,/,$(MODULE))


# Default agda arguments for `profile-module`
PROFILE_MODULE_AGDA_ARGS ?= --profile=definitions
# Target for profiling the typechecking a single module
.PHONY: profile-module
profile-module:
	@if [ -z "$(MODULE)" ]; then \
		echo "\033[0;31mError: MODULE variable is not set.\033[0m"; \
		echo "\033[0;31mUsage: make check-module MODULE=\"YourModuleName\"\033[0m"; \
		exit 1; \
	fi
	@# Attempt to delete the interface file only if the build directory exists
	@echo "\033[0;32mAttempting to delete interface file for $(MODULE)\033[0m"
	@find $(BUILD_DIR) -type f -path "*/agda/src/$(MODULE_DIR).agdai" -exec rm -f {} \+ 2>/dev/null || \
		echo "\033[0;31m$(BUILD_DIR) directory does not exist, skipping deletion of interface files.\033[0m"
	@# Ensure the temporary directory exists
	@mkdir -p $(TEMP_DIR)
	@# Profile typechecking the module and capture the output in the temp directory, also display on terminal
	@echo "\033[0;32mProfiling typechecking of $(MODULE)\033[0m"
	@$(AGDA) $(PROFILE_MODULE_AGDA_ARGS) src/$(MODULE_DIR).lagda.md 2>&1 | tee $(TEMP_DIR)/typecheck_output.txt
	@# Check for additional modules being typechecked by looking for any indented "Checking" line
	@if grep -E "^\s+Checking " $(TEMP_DIR)/typecheck_output.txt > /dev/null; then \
		echo "\033[0;31mOther modules were also checked. Repeating profiling after deleting interface file again.\033[0m"; \
		find $(BUILD_DIR) -type f -path "*/agda/src/$(MODULE_DIR).agdai" -exec rm -f {} \+; \
		$(AGDA) $(PROFILE_MODULE_AGDA_ARGS) src/$(MODULE_DIR).lagda.md; \
	else \
		echo "\033[0;32mOnly $(MODULE) was checked. Profiling complete.\033[0m"; \
	fi

	@# Cleanup
	@rm -f $(TEMP_DIR)/typecheck_output.txt



agda-html: ./src/everything.lagda.md
	@rm -rf ./docs/
	@mkdir -p ./docs/
	@${AGDA} ${AGDAHTMLFLAGS} ./src/everything.lagda.md

SUMMARY.md: ${AGDAFILES} ./scripts/generate_main_index_file.py
	@python3 ./scripts/generate_main_index_file.py

MAINTAINERS.md: ${CONTRIBUTORS_FILE} ./scripts/generate_maintainers.py
	@python3 ./scripts/generate_maintainers.py

CONTRIBUTORS.md: ${AGDAFILES} ${CONTRIBUTORS_FILE} ./scripts/generate_contributors.py
	@python3 ./scripts/generate_contributors.py

website/css/Agda-highlight.css: ./scripts/generate_agda_css.py ./theme/catppuccin.css
	@python3 ./scripts/generate_agda_css.py

.PHONY: website-prepare
website-prepare: agda-html ./SUMMARY.md ./CONTRIBUTORS.md ./MAINTAINERS.md ./website/css/Agda-highlight.css
	@cp $(METAFILES) ./docs/
	@mkdir -p ./docs/website
	@cp -r ./website/images ./docs/website/
	@cp -r ./website/css ./docs/website/
	@cp -r ./website/js ./docs/website/
	@cp -r ./tables ./docs

.PHONY: website
website: website-prepare
	@mdbook build

.PHONY: serve-website
serve-website: website-prepare
	@mdbook serve -p 8080 --open -d ./book/html

docs/dependency.dot : ./src/everything.lagda.md ${AGDAFILES}
	${AGDA} ${AGDAHTMLFLAGS} --dependency-graph=$@ $<

.PHONY: graph
graph: docs/dependency.dot

.PHONY: clean
clean:
	@rm -Rf ./_build/ ./book/ ./docs/

.PHONY: pre-commit
pre-commit:
	@pre-commit run --all-files
	@echo
	@echo Typechecking library
	@make check

# Keep versions in sync with .github/workflows/pages.yaml
install-website-dev:
	@cargo install mdbook@0.4.34
	@cargo install mdbook-linkcheck@0.7.7
	@cargo install mdbook-katex@0.5.7
	@cargo install mdbook-pagetoc@0.1.7
	@cargo install mdbook-catppuccin@1.2.0

.PHONY: unused-imports
unused-imports:
	python3 ./scripts/remove_unused_imports.py
	python3 ./scripts/demote_foundation_imports.py