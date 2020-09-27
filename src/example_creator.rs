// use egg::{RecExpr, SymbolLang};
// use crate::eggstentions::expression_ops::{IntoTree, Tree};
// use crate::thesy_parser::parser::Definitions;
// use std::collections::HashSet;
//
// /// Recieve expression `exp` representing the type and check if it is a function
// fn is_function_type(exp: RecExpr<SymbolLang>) -> bool  {
//     exp.into_tree().root().op.to_string() == "->"
// }
//
// // /// Recieve expression `exp` representing the type and check if it is a recursive function
// // fn is_recursive_function(exp: RecExpr<SymbolLang>) = identifier.annotation match {
// // case Some(annotation) => annotation.root == Language.mapTypeId && annotation.subtrees.dropRight(1).contains(annotation.subtrees.last)
// // case None => false
// // }
//
// fn types(definitions: Definitions) -> HashSet<RecExpr<SymbolLang>> {
//     definitions.datatypes.iter().flat_map(|d| d.constructors.iter().chain() vocab.definitions.flatMap(_.getType)
// }
//
// fn createAutoVar(RecExpr<SymbolLang>) AnnotatedTree => AnnotatedTree = {
// val counter = mutable.Map.empty[AnnotatedTree, Int].withDefault(_ => 0)
// (varType: AnnotatedTree) => {
// counter(varType) = counter(varType) + 1
// AnnotatedTree.identifierOnly(Identifier(
// literal = s"examplevar_${counter(varType)}_type_{${Programs.termToString(varType)}}",
// annotation = Some(varType)))
// }
// }
//
// private val placeholders: Map[AnnotatedTree, Seq[Identifier]] =
// types.flatMap({
// case AnnotatedTree(Language.mapTypeId, subtrees, _) => subtrees
// case i => Seq(i)
// }).map(t => (t, 0 until placeholderCount map (i => createPlaceholder(t, i)))).toMap
// logger.warn(s"Created total: ${placeholders.values.flatten.size}")
//
// private val examples: Map[AnnotatedTree, Seq[AnnotatedTree]] = {
// val rand = new scala.util.Random(1)
// vocab.datatypes.map(d => {
// val all: Seq[mutable.Set[AnnotatedTree]] = 0 until exampleDepthLimit map (_ => mutable.Set.empty[AnnotatedTree])
// // This is important so the prover will be sound
// all(0) ++= (d.constructors.filterNot(c => isRecursiveType(c)).map(t => AnnotatedTree.identifierOnly(t)).toSet)
// // Need to take many variations so wont fall with stuff like reverse tree
// val functionConstructors = d.constructors.filter(c => isRecursiveType(c))
// def createExample(const: Identifier, depth: Int): AnnotatedTree = {
// if (depth == 0) all(0).toSeq(rand.nextInt(all(0).size))
// else {
// val example = AnnotatedTree.withoutAnnotations(const, const.annotation.get.subtrees.dropRight(1).map({
// case t if t == d.asType =>
// createExample(functionConstructors(rand.nextInt(functionConstructors.size)), depth - 1)
// case t =>
// createAutoVar(t)
// }))
// all(depth) += example
// example
// }
// }
// functionConstructors.foreach(createExample(_, exampleDepthLimit - 1))
// (d.asType, all.flatten)
// }).toMap
// }
