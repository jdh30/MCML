module MCML.WPFEditor

open System.Windows
open MCML.Collections
open MCML.Errors

module DockPanel =
  let add (panel: Controls.Panel) ctrl dock =
    Controls.DockPanel.SetDock(ctrl, dock)
    panel.Children.Add ctrl
    |> ignore

let forward = Documents.LogicalDirection.Forward

let lengthOfInline (inl: Documents.Inline) =
  match inl with
  | :? Documents.LineBreak -> 2
  | :? Documents.Run as run -> inl.ContentStart.GetTextRunLength forward
  | _ -> failwithf "Unknown inline %A" inl

type Documents.FlowDocument with
  member d.GetPointerFromCharOffset charOffset =
    let mutable count = charOffset
    let mutable inl = (Seq.head d.Blocks :?> Documents.Paragraph).Inlines.FirstInline
    while not(isNull inl) && lengthOfInline inl < count do
      count <- count - lengthOfInline inl
      inl <- inl.NextInline
    if isNull inl then d.ContentEnd else
      inl.ContentStart.GetPositionAtOffset(count, forward)

type Controls.RichTextBox with
  /// Get or set the text as a string.
  member c.WholeTextRange =
    let d = c.Document
    Documents.TextRange(d.ContentStart, d.ContentEnd)
  /// TextPointer at given index.
  member c.At i =
    c.Document.GetPointerFromCharOffset i
  /// Set the caret position to the given index.
  member c.Goto i =
    c.CaretPosition <- c.At i
  /// Select text from the first index to the second index.
  member c.Select(first, last) =
    c.Selection.Select(c.At first, c.At last)
  /// Clear all highlights.
  member c.ClearHighlights() =
    c.WholeTextRange.ClearAllProperties()
  /// Highlight text between the first index and the second index.
  member c.Highlight(first, last, brush) =
    let textRange = Documents.TextRange(c.At first, c.At last)
    textRange.ApplyPropertyValue(Documents.TextElement.BackgroundProperty, brush)
  /// Get or set the text as a string.
  member c.Text
    with get() = c.WholeTextRange.Text
    and set text =
      c.Document.Blocks.Clear()
      Documents.Run text
      |> Documents.Paragraph
      |> c.Document.Blocks.Add
  /// Find the index into the string of the given text pointer.
  member c.IndexOfTextPointer p =
    Documents.TextRange(c.Document.ContentStart, p).Text.Length
  /// Find the text pointer closest to the given coordinate.
  member c.TryGetIndexFromPoint p =
    match c.GetPositionFromPoint(p, false) with
    | null -> None
    | p -> Some(c.IndexOfTextPointer p)

let app = Application()
let window = Window()
let pane = Controls.DockPanel()
let scroll = Controls.ScrollViewer()
let editor = Controls.RichTextBox()
let tabs = Controls.TabControl()
let errors = Controls.Label()
let repl = Controls.Label()
let typeThrowbackLabel = Controls.Label()
let typeThrowback = Controls.Primitives.Popup(Child=typeThrowbackLabel)

let mutable clickFeedback = fun () -> ()

let setFeedback first last =
  clickFeedback <- fun () ->
    let _ = editor.Focus()
    editor.Select(first, last)
    editor.Goto first

module Env = TypeInference.Env

let typeAt = Dictionary<int, AST.Type> HashIdentity.Structural

open Parser

let updateTypeAt (typeOfPos: Dictionary<AST.Pos, _>) =
  typeAt.Clear()
  let len = Dictionary HashIdentity.Structural
  for KeyValue(pos, ty) in typeOfPos do
    for i in pos.Start .. pos.End do
      match Dictionary.tryFind i len with
      | Some len when len < pos.End-pos.Start -> ()
      | _ ->
          typeAt.[i] <- ty
          len.[i] <- pos.End - pos.Start

let eval (input: string) =
  match Interpreter.parseAndRun input with
  | Ok(tokens, vars, stmts, typeOfPos) ->
      updateTypeAt typeOfPos
      errors.Content <- ""
      errors.Background <- Media.Brushes.LightGreen
      repl.Content <-
        match vars.Local with
        | [] -> ""
        | (name, (pos, valueRef))::_ ->
            let ty =
              match Dictionary.tryFind pos typeOfPos with
              | None -> "?"
              | Some ty -> AST.Type.toString ty
            sprintf "val %s : %s = %s" name ty (Interpreter.stringOfValue !valueRef)
      clickFeedback <- (fun () -> ())
      editor.ClearHighlights()
  | Error(msg, posn, typeOfPos) ->
      updateTypeAt typeOfPos
      errors.Background <- Media.Brushes.LightSalmon
      let line =
        1 + Seq.length (Seq.filter ((=) '\n') (input.Substring(0, posn.Start)))
      let msg =
        match msg with
        | UnexpectedInput -> "Unexpected input"
        | EndOfInputInsideString -> "End of input inside string literal (missing \")"
        | EndOfInputInsideComment -> "End of input inside comment (missing '*)')"
        | Expected s -> sprintf "Expected %s" s
        | Dummy -> failwithf "Internal error: Dummy escaped!"
        | CyclicType(ty1, ty2) ->
            let ty1, ty2 = AST.Type.toString2 ty1 ty2
            sprintf "Unifying %s ≡ %s would result in a cyclic type (break the cycle using a union type)" ty1 ty2
        | TupleLengthsDiffer(ty1, ty2) ->
            let ty1, ty2 = AST.Type.toString2 ty1 ty2
            sprintf "Different tuple lengths in %s ≠ %s" ty1 ty2
        | TypeMismatch(ty1, ty2) ->
            let ty1, ty2 = AST.Type.toString2 ty1 ty2
            sprintf "Type mismatch %s ≠ %s" ty1 ty2
        | DuplicatePatternName p -> sprintf "Variable name '%s' is bound more than once in this pattern" p
        | MissingPatternName p -> sprintf "Variable name '%s' must appear on both sides of this or-pattern" p
        | UnknownConstructor c -> sprintf "Unknown constructor '%s'" c
        | UnknownVariable x -> sprintf "Unknown variable '%s'" x
        | UnknownType x -> sprintf "Unknown type '%s'" x
        | UnknownTypeVariable -> "Unknown type variable"
        | ConstructorRequiresArgument ty ->
            sprintf "Constructor requires an argument of type %s" (AST.Type.toString ty)
        | ConstructorDoesNotRequireArgument -> "Constructor does not require an argument"
        | Unmatched value -> sprintf "Value %s fell through all patterns" value
        | Panic msg -> sprintf "PANIC: %s" msg
      errors.Content <- sprintf "%s at line %d" msg line
      setFeedback posn.Start posn.End
      editor.ClearHighlights()
      editor.Highlight(posn.Start, posn.End, Media.Brushes.Salmon)

let mutable lastText =
#if INTERACTIVE
  System.IO.Path.Combine[|__SOURCE_DIRECTORY__; "Examples.fsx"|]
  |> System.IO.File.ReadAllText
#else
  let ass = System.Reflection.Assembly.GetExecutingAssembly()
  use stream = ass.GetManifestResourceStream "MCML.Examples.fsx"
  use reader = new System.IO.StreamReader(stream)
  reader.ReadToEnd()
#endif
  |> fun s -> s.Replace("\r", "")

[<EntryPoint; System.STAThread>]
let main args =
  window.Title <- "Integrated Development Environment"
  window.Content <- pane
  DockPanel.add pane scroll Controls.Dock.Bottom
  DockPanel.add pane editor Controls.Dock.Top
  let _ = pane.Children.Add typeThrowback
  scroll.Content <- tabs
  let _ = tabs.Items.Add(Controls.TabItem(Header="Errors", Content=errors))
  let _ = tabs.Items.Add(Controls.TabItem(Header="REPL", Content=repl))
  errors.MouseUp.Add(fun _ -> clickFeedback())
  editor.AcceptsReturn <- true
  editor.PreviewKeyDown.Add(fun e ->
    if e.Key = Input.Key.Enter then
      let newPointer = editor.Selection.Start.InsertLineBreak()
      editor.Selection.Select(newPointer, newPointer)
      e.Handled <- true)
  editor.VerticalScrollBarVisibility <- Controls.ScrollBarVisibility.Visible
  editor.FontFamily <- Media.FontFamily("Consolas")
  editor.FontSize <- 14.0
  editor.TextChanged.Add(fun e ->
    let newText = editor.Text
    if newText <> lastText then
      lastText <- newText
      try
        eval editor.Text
      with e ->
        let s = sprintf "%s\n%s" e.Message e.StackTrace
        printfn "%s" s
    )
  editor.Text <- lastText
  editor.MouseMove.Add(fun e ->
    let p = e.GetPosition window
    let clear() =
      typeThrowback.IsOpen <- false
      typeThrowback.StaysOpen <- false
    match editor.TryGetIndexFromPoint p with
    | None -> clear()
    | Some i ->
        match Dictionary.tryFind i typeAt with
        | None -> clear()
        | Some ty ->
            typeThrowback.IsOpen <- true
            let tb = Controls.TextBlock(Text=AST.Type.toString ty)
            tb.FontFamily <- Media.FontFamily "Arial"
            tb.FontSize <- 12.0
            tb.Foreground <- Media.Brushes.Black
            tb.Background <- Media.Brushes.SeaShell
            typeThrowbackLabel.Content <- tb
            typeThrowbackLabel.Background <- Media.Brushes.SeaShell
            typeThrowbackLabel.BorderBrush <- Media.Brushes.LightGray
            typeThrowbackLabel.BorderThickness <- Thickness(Left=1.0, Top=1.0, Right=3.0, Bottom=3.0)
            typeThrowback.StaysOpen <- true
            typeThrowback.Placement <- Controls.Primitives.PlacementMode.RelativePoint
            typeThrowback.PlacementTarget <- editor
            typeThrowback.HorizontalOffset <- p.X + 0.
            typeThrowback.VerticalOffset <- p.Y + 14.)
  typeThrowback.MouseEnter.Add(fun _ ->
    typeThrowback.IsOpen <- false
    typeThrowback.StaysOpen <- false)
  typeThrowbackLabel.Margin <- Thickness 3.0
  typeThrowback.AllowsTransparency <- true
  let _ = editor.Focus()
  app.Run window
