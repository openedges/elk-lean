import Elk.Json
import Elk.Text.Lexer
import Elk.Text.Parser
import Elk.Text.Loader
/-!
# `org.eclipse.elk.graph.text`: the ELK Text (`.elkt`) format

* `Elk.Text.Lexer`  : tokeniser for the terminals of `ElkGraph.xtext`.
* `Elk.Text.Parser` : recursive-descent parser producing a syntax tree (`parseAst`).
* `Elk.Text.Loader` : linking and `ElkGraph` construction (`parseElkt`, `loadAst`, `applyDefaults`).
-/
