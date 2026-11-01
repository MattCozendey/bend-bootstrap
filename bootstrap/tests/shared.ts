// What the scripts of the tests have in common.

// types

// a command and how it runs, as Bun.spawnSync takes them
type Command = Bun.SpawnOptions.SpawnSyncOptions<
  "ignore",
  Bun.SpawnOptions.Readable,
  Bun.SpawnOptions.Readable
> & { readonly cmd: string[] };

// functions

// the arguments of the script, one for each name; with another number of them, the script stops
// and prints its usage
export const getArgs = <const T extends readonly string[]>(
  ...names: T
): { readonly [K in keyof T]: string } => {
  const args = process.argv.slice(2);
  if (args.length !== names.length) {
    console.error(`usage: bun ${process.argv[1]} ${names.join(" ")}`);
    process.exit(1);
  }
  return args as { readonly [K in keyof T]: string };
};

// runs a command that must succeed, its output to ours unless it says otherwise; on a failure, the
// script stops with the command's exit code
export const run = ({ cmd, ...options }: Command): void => {
  const { success, exitCode } = Bun.spawnSync(cmd, {
    stdout: "inherit",
    stderr: "inherit",
    ...options,
  });
  if (!success) process.exit(exitCode || 1);
};
