/-
  Bedrock client for the LLM proposer (ported from lean-green's
  `LeanBlack/Bedrock.lean`, the artifact that first ran an LLM
  proposer from inside Lean).

  Wraps `aws bedrock-runtime invoke-model` and parses the Anthropic-
  on-Bedrock response shape. Body and response are written through
  temp files (the CLI takes the request body via `fileb://...` and
  writes the response to a positional path).

  Dependencies: the `aws` CLI on PATH, AWS credentials in the standard
  chain, Bedrock access in the configured region.
-/

import Lean.Data.Json

namespace LeanBlack.Bedrock

open Lean (Json)

structure Config where
  region    : String := "us-east-1"
  modelId   : String := "us.anthropic.claude-sonnet-5"
  -- Sonnet 5 runs adaptive thinking by default (when `thinking` is
  -- omitted), so thinking tokens count against maxTokens — give the
  -- proposal + GuardSpec proof ample headroom.
  maxTokens : Nat    := 16000
  bodyPath  : String := "/tmp/lean-sage-bedrock-body.json"
  outPath   : String := "/tmp/lean-sage-bedrock-out.json"

def defaultConfig : Config := {}

/-- Build the request body in Bedrock/Anthropic Messages API format. -/
private def bodyJson (cfg : Config) (prompt : String) : Json :=
  Json.mkObj [
    ("anthropic_version", Json.str "bedrock-2023-05-31"),
    ("max_tokens", Lean.toJson cfg.maxTokens),
    ("messages", Json.arr #[
      Json.mkObj [("role", Json.str "user"), ("content", Json.str prompt)]
    ])
  ]

/-- Concatenate every `text` block in the response, skipping non-text
    blocks. Sonnet 5+ runs adaptive thinking by default, so the content
    array may lead with a `thinking` block (which has no `text` field)
    before the text — grabbing `content[0]` would fail there. -/
private def extractText (j : Json) : Except String String := do
  let content ← j.getObjVal? "content"
  let arr ← content.getArr?
  let texts := arr.filterMap fun b =>
    match b.getObjVal? "text" >>= Json.getStr? with
    | .ok s => some s
    | .error _ => none
  let joined := texts.foldl (· ++ ·) ""
  if joined.isEmpty then
    .error "no text block in response.content"
  else
    .ok joined

/-- Make a single Bedrock call and return the model's text or an error
    describing what went wrong (CLI failure, JSON parse, or unexpected
    response shape). -/
def invoke (cfg : Config) (prompt : String) : IO (Except String String) := do
  IO.FS.writeFile cfg.bodyPath (bodyJson cfg prompt).pretty
  let out ← IO.Process.output {
    cmd := "aws"
    args := #[
      "bedrock-runtime", "invoke-model",
      "--region", cfg.region,
      "--model-id", cfg.modelId,
      "--content-type", "application/json",
      "--body", "fileb://" ++ cfg.bodyPath,
      cfg.outPath
    ]
  }
  if out.exitCode != 0 then
    return .error s!"aws CLI failed (exit {out.exitCode}):\n{out.stderr}"
  let respText ← IO.FS.readFile cfg.outPath
  match Json.parse respText with
  | .error e => return .error s!"JSON parse failed: {e}\nresponse was: {respText}"
  | .ok json => return extractText json

end LeanBlack.Bedrock
