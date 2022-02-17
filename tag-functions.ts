// We can use a template string to create a special kind of function known as a tag function.
// We can use a tag function to extend or modify the standard behavior of template strings.
// When we apply a tag function to a template string, the template string becomes a tagged template.

// We are going to implement a tag function named htmlEscape. To use a tag function, we must use the name of the function, followed by a template string:
// let html = htmlEscape`<h1>${name} ${surname}</h1>`;

// The signature of a tag function appears as follows:

// tag(literals: TemplateStringsArray, ...placeholders: any[]): string;
// where templateStringsArray is all static literals in the template string (<h1></h1> in the prev example) as the first arg
// and the ...(rest) parameter as the second parameter, containing all the values in the template string (name and surname in the prev example)

function htmlEscape(literals: TemplateStringsArray, ...placeholders: any[]) {
  let result = "";
  for (let i = 0; i < placeholders.length; i++) {
    result += literals[i];
    result += placeholders[i]
      .replace(/&/g, "&amp;")
      .replace(/"/g, "&quot;")
      .replace(/"/g, "'")
      .replace(/</g, "&lt;")
      .replace(/>/g, "&gt;");
  }
  result += literals[literals.length - 1];
  return result;
}
