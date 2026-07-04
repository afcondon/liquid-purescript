import { spawnSync } from "node:child_process";

export const runZ3Impl = (input) => () => {
  const r = spawnSync("z3", ["-in"], { input, encoding: "utf8" });
  if (r.error) {
    throw new Error("failed to run z3: " + r.error.message);
  }
  return (r.stdout || "") + (r.stderr || "");
};
