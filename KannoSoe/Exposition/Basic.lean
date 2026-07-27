import Lean

namespace KannoSoe.Exposition

/-!
Basic document data for the prose-facing Exposition layer.

The layer is deliberately downstream of the checked grid library: documents
may cite declarations, glossary terms, and other documents, but they define no
grid vocabulary and prove no grid facts.
-/

abbrev DocId := String

inductive Inline where
  | text (s : String)
  | anchor (name : Lean.Name)
  | code (s : String)
  | term (s : String)
  | xref (target : DocId) (label : String)
deriving Repr

inductive ClaimStatus where
  | checked
  | proseBound (reason : String)
deriving Repr

structure Claim where
  inlines : List Inline
  status : ClaimStatus
  anchors : List Lean.Name := []
deriving Repr

inductive Block where
  | para (inlines : List Inline)
  | claimPara (claim : Claim)
  | quote (blocks : List Block)
  | table (headers : List String) (rows : List (List String))
  | list (items : List (List Inline))
  | heading (level : Nat) (inlines : List Inline)
  | raw (markdown : String)
deriving Repr

structure Section where
  id : DocId
  title : String
  blocks : List Block := []
deriving Repr

structure Doc where
  id : DocId
  title : String
  output : String
  source : String
  summary : String := ""
  blocks : List Block := []
  sections : List Section := []
  footer : List Block := []
deriving Repr

def markdownEscape (s : String) : String :=
  (((s.replace "\\" "\\\\").replace "|" "\\|").replace "\n" " ").replace "\r" " "

def joinComma : List String -> String
  | [] => ""
  | x :: rest => rest.foldl (fun acc item => acc ++ ", " ++ item) x

def renderAnchors (anchors : List Lean.Name) : String :=
  match anchors with
  | [] => "—"
  | names => joinComma (names.map (fun name => "`" ++ name.toString ++ "`"))

def renderInline : Inline -> String
  | .text s => s
  | .anchor name => "`" ++ name.toString ++ "`"
  | .code s => "`" ++ s ++ "`"
  | .term s => s
  | .xref target label => "[" ++ label ++ "](" ++ target ++ ")"

def renderInlines (inlines : List Inline) : String :=
  String.intercalate "" (inlines.map renderInline)

def renderClaim (claim : Claim) : String :=
  let body := renderInlines claim.inlines
  match claim.status with
  | .checked =>
      match claim.anchors with
      | [] => body
      | anchors => body ++ " *(checked: " ++ renderAnchors anchors ++ ")*"
  | .proseBound reason =>
      let anchorSuffix :=
        match claim.anchors with
        | [] => ""
        | anchors => "; anchors: " ++ renderAnchors anchors
      body ++ " *(prose-bound: " ++ reason ++ anchorSuffix ++ ")*"

def renderTableRow (cells : List String) : String :=
  "| " ++ String.intercalate " | " (cells.map markdownEscape) ++ " |"

def renderTable (headers : List String) (rows : List (List String)) : String :=
  let header := renderTableRow headers
  let rule := renderTableRow (headers.map (fun _ => "---"))
  String.intercalate "\n" (header :: rule :: rows.map renderTableRow)

mutual
  def renderBlock : Block -> String
    | .para inlines => renderInlines inlines
    | .claimPara claim => renderClaim claim
    | .quote blocks =>
        let body := renderBlocks blocks
        String.intercalate "\n" ((body.splitOn "\n").map (fun line => "> " ++ line))
    | .table headers rows => renderTable headers rows
    | .list items =>
        String.intercalate "\n" (items.map (fun item => "- " ++ renderInlines item))
    | .heading level inlines =>
        String.ofList (List.replicate level '#') ++ " " ++ renderInlines inlines
    | .raw markdown => markdown

  def renderBlocks : List Block -> String
    | [] => ""
    | blocks => String.intercalate "\n\n" (blocks.map renderBlock)
end

def renderSection (sec : Section) : String :=
  "## " ++ sec.title ++ "\n\n" ++ renderBlocks sec.blocks

def generatedHeader (doc : Doc) : String :=
  "<!-- GENERATED from " ++ doc.source ++
    " by `lake exe exposition_gen` - do not edit -->\n\n"

def renderDoc (doc : Doc) : String :=
  let bodyParts :=
    [renderBlocks doc.blocks] ++ doc.sections.map renderSection ++ [renderBlocks doc.footer]
  let body := String.intercalate "\n\n" (bodyParts.filter (fun part => part != ""))
  generatedHeader doc ++ body

namespace Inline

def anchors : Inline -> List Lean.Name
  | .anchor name => [name]
  | _ => []

def terms : Inline -> List String
  | .term t => [t]
  | _ => []

def xrefs : Inline -> List DocId
  | .xref target _ => [target]
  | _ => []

end Inline

namespace Claim

def allAnchors (claim : Claim) : List Lean.Name :=
  claim.anchors ++ claim.inlines.flatMap Inline.anchors

def terms (claim : Claim) : List String :=
  claim.inlines.flatMap Inline.terms

def xrefs (claim : Claim) : List DocId :=
  claim.inlines.flatMap Inline.xrefs

end Claim

mutual
  def Block.anchors : Block -> List Lean.Name
    | .para inlines => inlines.flatMap Inline.anchors
    | .claimPara claim => claim.allAnchors
    | .quote blocks => Block.listAnchors blocks
    | .table _ _ => []
    | .list items => items.flatMap (fun item => item.flatMap Inline.anchors)
    | .heading _ inlines => inlines.flatMap Inline.anchors
    | .raw _ => []

  def Block.listAnchors : List Block -> List Lean.Name
    | [] => []
    | block :: blocks => block.anchors ++ Block.listAnchors blocks
end

mutual
  def Block.claims : Block -> List Claim
    | .claimPara claim => [claim]
    | .quote blocks => Block.listClaims blocks
    | _ => []

  def Block.listClaims : List Block -> List Claim
    | [] => []
    | block :: blocks => block.claims ++ Block.listClaims blocks
end

mutual
  def Block.terms : Block -> List String
    | .para inlines => inlines.flatMap Inline.terms
    | .claimPara claim => claim.terms
    | .quote blocks => Block.listTerms blocks
    | .table _ _ => []
    | .list items => items.flatMap (fun item => item.flatMap Inline.terms)
    | .heading _ inlines => inlines.flatMap Inline.terms
    | .raw _ => []

  def Block.listTerms : List Block -> List String
    | [] => []
    | block :: blocks => block.terms ++ Block.listTerms blocks
end

mutual
  def Block.xrefs : Block -> List DocId
    | .para inlines => inlines.flatMap Inline.xrefs
    | .claimPara claim => claim.xrefs
    | .quote blocks => Block.listXrefs blocks
    | .table _ _ => []
    | .list items => items.flatMap (fun item => item.flatMap Inline.xrefs)
    | .heading _ inlines => inlines.flatMap Inline.xrefs
    | .raw _ => []

  def Block.listXrefs : List Block -> List DocId
    | [] => []
    | block :: blocks => block.xrefs ++ Block.listXrefs blocks
end

namespace Section

def anchors (sec : Section) : List Lean.Name :=
  Block.listAnchors sec.blocks

def claims (sec : Section) : List Claim :=
  Block.listClaims sec.blocks

def terms (sec : Section) : List String :=
  Block.listTerms sec.blocks

def xrefs (sec : Section) : List DocId :=
  Block.listXrefs sec.blocks

end Section

namespace Doc

def anchors (doc : Doc) : List Lean.Name :=
  Block.listAnchors doc.blocks ++
    doc.sections.flatMap Section.anchors ++
    Block.listAnchors doc.footer

def claims (doc : Doc) : List Claim :=
  Block.listClaims doc.blocks ++
    doc.sections.flatMap Section.claims ++
    Block.listClaims doc.footer

def terms (doc : Doc) : List String :=
  Block.listTerms doc.blocks ++
    doc.sections.flatMap Section.terms ++
    Block.listTerms doc.footer

def xrefs (doc : Doc) : List DocId :=
  Block.listXrefs doc.blocks ++
    doc.sections.flatMap Section.xrefs ++
    Block.listXrefs doc.footer

end Doc

end KannoSoe.Exposition
