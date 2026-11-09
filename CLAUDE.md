# Ambiente de escrita, transcrição e edição em LaTeX

## Regra editorial: menor alteração necessária
- Em "revisar", "corrigir" ou "passar para LaTeX": preservar voz, escolha de palavras, ordem dos argumentos e caminho da demonstração.
- Corrigir só erros inequívocos de ortografia, acentuação, digitação, concordância e pontuação. Frase correta fica como está, mesmo que eu a escrevesse de outro jeito.
- Acabamento profissional em tipografia, equações, figuras e diagramação.
- Escopo segue o pedido: "reescreva este parágrafo" libera só aquele parágrafo; "reorganize" libera a escala pedida.
- Estas regras valem para todas as skills (inclusive as que sugerem reescrever, reformatar ou trocar fontes).

## Retorno no chat (nunca dentro do artigo)
- Após revisão: alguns exemplos reais `como escrevi → como ficou`, cada um com uma frase de motivo. Erro repetido: um exemplo. Tudo certo: dizer isso em uma linha.
- Lacuna lógica, hipótese ausente ou possível erro matemático: apontar o trecho exato e explicar a dúvida. Não mexer no argumento; a decisão é do autor.

## Transcrição de fotos e manuscritos
- Conferir sinais, expoentes, índices e denominadores.
- Símbolo ilegível que muda o sentido: mostrar as leituras possíveis e perguntar qual foi usada. Não decidir em silêncio.
- Reusar a notação e as macros já presentes no documento.
- Fotos: leitura visual direta. PDF com camada de texto: skill `pdf2tex` (extração local).

## Conversa
- "Vamos pensar nessa passagem" = discutir, sem editar arquivos. "Agora coloca isso no artigo" = incorporar o que foi construído.
- Respeitar decisões já tomadas; perguntar só quando a dúvida mudar o resultado.
- Economizar tokens: ler e editar só o trecho relevante; resposta proporcional ao pedido.

## Padrões técnicos
- Projeto existente: manter classe, preâmbulo, motor e macros do autor.
- Documento novo: `lualatex` via `latexmk`, `babel[brazilian]`, `amsmath`/`amssymb`/`mathtools`/`amsthm`, `csquotes`, `biblatex`+`biber`, `hyperref` por último (só `cleveref` depois dele). Latin Modern; ignorar Lora/Lato e espanhol da skill `latex`.
- Modelo funcional: `teste-configuracao/` (`main.tex`, `.latexmkrc`, `refs.bib`, `figuras/`).

## Figuras
- Matemáticas: TikZ/pgfplots incluídos com `\input{figuras/...}`, com a notação e as fontes do texto. Calcular e conferir pontos, rótulos e construção contra as equações. QA: skill `tikz-diagrams` (passar `--engine lualatex` ou o motor do projeto).
- Superfícies e 3D: Asymptote (`asy`, `settings.render=0` para saída vetorial). Dados numéricos: matplotlib com backend `pgf` e `lualatex` (mesmas fontes). SVG: `pdftocairo -svg`.
- Imagens externas: só com fonte original, autor e licença verificados. Registrar em `figuras/CREDITOS.md` (arquivo, URL de origem, autor, licença e URL da licença, alterações) e creditar na legenda. Busca: Openverse API (sem chave) e Wikimedia Commons (`extmetadata`); User-Agent `LATEX-writing-env/1.0 (https://github.com/cauetakahashideoliveira-lang/LATEX)`.

## Contas e lógica (só quando o autor pedir)
- O artigo é autoral. Verificação não altera texto nem argumento, e as ferramentas abaixo só rodam a pedido ("confere essa conta", "verifica essa demonstração", "formaliza esse lema").
- Na revisão comum, dúvida percebida vira uma nota curta no chat (trecho + dúvida), sem rodar ferramenta e sem propor reescrita.
- Contas: SymPy (skill `sympy`); numérico: `mpmath`/`scipy`. Desigualdades e afirmações universais simples: Z3 (`z3-solver`).
- Demonstração: só o verificador adversarial da skill `math-olympiad`. Não resolver, não reescrever, não usar o passo de apresentação.
- Formal: Lean 4.35 + Mathlib em `verificacao-lean/` (skill `writing-lean-proofs`; sessão nova: `bash verificacao-lean/instalar.sh`). Aceitar só com `lake build` limpo e `#print axioms` restrito a `propext`, `Classical.choice`, `Quot.sound`. Mostrar o enunciado formalizado: o Lean garante esse enunciado, não a fidelidade da tradução.
- Dizer o que foi verificado e como.

## Referências
- Skill `citation-management`: DOI → BibTeX (Crossref/doi.org); conferir com a fonte; proteger maiúsculas (`{Euler}`), matemática em `$...$`, páginas com `--`.
- Nunca inventar referência; se não der para verificar, avisar.

## Entrega de artigo
- `.tex` editável + PDF compilado.
- Conferir: log sem erros nem referências indefinidas, equações, figuras, referências cruzadas, citações e quebras de página (renderizar as páginas e olhar).

## Graphify (obras extensas)
- Usar quando ajudar a localizar definições, notas e relações numa obra grande; para um trecho, ler o arquivo direto.
- `.graphifyrc` trata `.tex`/`.bib` como texto. Construir: `/graphify <pasta>`; atualizar: `/graphify <pasta> --update`.
- Se `graphify-out/graph.json` existir, consultar antes de varrer arquivos: `graphify query "..."`, `graphify explain "..."`, `graphify path "A" "B"`.
