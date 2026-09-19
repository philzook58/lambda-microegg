import { readFileSync, readdirSync } from "node:fs";
import init, { run_wasm } from "../pkg/lambda_microegg.js";

await init({
  module_or_path: readFileSync(new URL("../pkg/lambda_microegg_bg.wasm", import.meta.url)),
});

const demoDirectory = new URL("../demos/", import.meta.url);
for (const name of readdirSync(demoDirectory).filter(name => name.endsWith(".sexp")).sort()) {
  const program = readFileSync(new URL(name, demoDirectory), "utf8");
  try {
    const output = run_wasm(program);
    if (output.length === 0) {
      throw new Error("demo produced no output");
    }
    if (name === "lambda.sexp" && !output.endsWith("(pair z z)")) {
      throw new Error(`unexpected extraction:\n${output}`);
    }
    console.log(`ok ${name}`);
  } catch (error) {
    throw new Error(`${name}: ${error}`);
  }
}
