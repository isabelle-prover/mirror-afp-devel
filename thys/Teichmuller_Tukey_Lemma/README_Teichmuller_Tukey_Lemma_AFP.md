# Teichmuller_Tukey_Lemma — preparação para o AFP

O subdiretório `Teichmuller_Tukey_Lemma` contém a estrutura-fonte da entrada:

- `Teichmuller_Tukey_Lemma.thy`: teoria e texto do documento;
- `ROOT`: sessão Isabelle, no capítulo `AFP`, com timeout de 600 segundos;
- `document/root.tex`: título, autores, afiliações e resumo;
- `document/root.bib`: referências do artigo-fonte e do livro de Shoenfield.

## Compilação de conferência

Use a versão corrente do Isabelle aceita pelo AFP. A partir do diretório pai
desta entrada, execute:

```sh
isabelle build -v -o browser_info -o "document=pdf" \
  -o "document_variants=document:outline=/proof,/ML" \
  -D Teichmuller_Tukey_Lemma
```

O comando deve terminar sem erros. Examine também o fim do log, onde aparecem
eventuais avisos do linter usado pelo AFP. O PDF é produzido no diretório de
saída de documentos configurado pela instalação do Isabelle.

## Empacotamento

Depois de uma compilação limpa, estando no diretório pai, gere o arquivo a
enviar pelo formulário do AFP com:

```sh
tar -czf Teichmuller_Tukey_Lemma.tar.gz Teichmuller_Tukey_Lemma
```

Não inclua diretórios de saída de compilação no arquivo compactado.

## Dados para o formulário

- **Título:** The Teichmüller–Tukey Lemma
- **Nome curto / sessão:** `Teichmuller_Tukey_Lemma`
- **Autores:** Vithor Lindermann Kraisch; Luiz Gustavo Cordeiro
- **Afiliação:** Department of Mobility Engineering, Federal University of
  Santa Catarina, Joinville, Brazil
- **Tópico sugerido:** Mathematics / Set theory
- **Licença:** os autores ainda devem escolher no formulário (BSD é a opção
  comum em entradas do AFP, mas a escolha é dos autores).
- **Mantenedor:** indicar ao menos um autor e seu endereço de e-mail.

Resumo para colar no formulário:

> This entry formalizes the Teichmüller–Tukey lemma in Isabelle/HOL: every
> nonempty family of sets of finite character has a member that is maximal
> under inclusion. Instead of deriving the result from Zorn's lemma, which is
> already available in Isabelle/HOL, the development follows the direct
> choice-function construction of Sun and Yu, originally formulated in
> Morse–Kelley set theory and checked in Coq. The Isabelle proof makes explicit
> the choice argument that turns a fixed point of the construction into a
> maximal member. The result is intended for use in a separate formalization
> of first-order logic following Shoenfield.

## Antes do envio

1. Confirmar com Vithor se o detalhe corrigido era realmente o passo final
   agora explicado antes do lema `\<X>_implies_TTL`. O arquivo o
   descreve como um passo implícito, não como um erro do artigo.
2. Informar e-mails dos autores/mantenedor no formulário e, se desejado, no
   cabeçalho da teoria.
3. Escolher a licença da entrada.
4. Executar exatamente o comando de conferência acima com a versão atual do
   Isabelle/AFP e corrigir qualquer aviso relevante do linter.
5. No comentário aos editores, explicar que a contribuição é a prova direta
   por função de escolha, e não apenas o enunciado, pois o resultado também é
   consequência imediata do lema de Zorn existente em HOL.
