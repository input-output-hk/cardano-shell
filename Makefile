PROJECT_NAME = cardano-shell

help: ## Print documentation
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | awk 'BEGIN {FS = ":.*?## "}; {printf "\033[36m%-30s\033[0m %s\n", $$1, $$2}'

stylish-haskell: ## Apply stylish-haskell on all *.hs files
	@find . -type f -name "*.hs" -not -path '.git' -not -path '*.stack-work*' -print0 | xargs -0 stylish-haskell -i

ghci: ## Run repl
	@stack ghci $(PROJECT_NAME):lib --haddock-deps --ghci-options=-fobject-code

ghcid:  ## Run ghcid
	@ghcid --command "stack ghci $(PROJECT_NAME):lib --ghci-options=-fobject-code"

run-test: ## Build & run test
	@stack build --fast && \
	stack test --fast

test-ghci: ## Run repl on test suites
	@stack ghci $(PROJECT_NAME):lib $(PROJECT_NAME):test:$(PROJECT_NAME)-test --ghci-options=-fobject-code

test-ghcid: ## Run ghcid on test suites
	@ghcid --command "stack ghci $(PROJECT_NAME):lib $(PROJECT_NAME):test:$(PROJECT_NAME)-test --ghci-options=-fobject-code"

.PHONY: stylish-haskell ghcid ghcid-test run-test test-ghci test-ghcid help