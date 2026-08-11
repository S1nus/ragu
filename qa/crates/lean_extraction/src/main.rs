mod driver;
mod expr;
mod fingerprint;
mod instance;
mod instances;
mod linexp;
mod sha256;

use std::{
    fs,
    path::{Path, PathBuf},
    process::ExitCode,
};

use clap::{Parser, Subcommand};
use instance::CircuitInstance;

use crate::instances::{
    boolean_alloc::BooleanAllocInstance,
    boolean_and::BooleanAndInstance,
    boolean_conditional_enforce_equal::BooleanConditionalEnforceEqualInstance,
    boolean_conditional_select::BooleanConditionalSelectInstance,
    core_mul::CoreMulInstance,
    element_alloc::ElementAllocInstance,
    element_alloc_square::ElementAllocSquareInstance,
    element_div_nonzero::ElementDivNonzeroInstance,
    element_enforce_nonzero::ElementEnforceNonzeroInstance,
    element_enforce_root_of_unity::{
        ElementEnforceRootOfUnityInstanceK2, ElementEnforceRootOfUnityInstanceK5,
    },
    element_enforce_zero::ElementEnforceZeroInstance,
    element_fold::{ElementFoldInstanceN3, ElementFoldInstanceN7},
    element_invert::ElementInvertInstance,
    element_invert_with::ElementInvertWithInstance,
    element_is_equal::ElementIsEqualInstance,
    element_is_zero::ElementIsZeroInstance,
    element_mul::ElementMulInstance,
    element_square::ElementSquareInstance,
    endoscalar_alloc::EndoscalarAllocInstance,
    endoscalar_group_scale::EndoscalarGroupScaleInstance,
    endoscalar_lift::EndoscalarLiftInstance,
    nonzero_bank_scope::NonzeroBankScopeInstanceK2,
    point_add_incomplete::PointAddIncompleteInstance,
    point_alloc::{PointAllocInstanceFp, PointAllocInstanceFq},
    point_conditional_endo::PointConditionalEndoInstance,
    point_conditional_negate::PointConditionalNegateInstance,
    point_double::PointDoubleInstance,
    point_double_and_add_incomplete::PointDoubleAndAddIncompleteInstance,
};

struct ExportTarget {
    /// Lean module name of the (handwritten) formal instance.
    name: &'static str,
    /// Computes the canonical digest of the instance's extracted trace.
    fingerprint: fn() -> String,
}

/// Single source of truth for every exported instance: `export`, `check` and
/// `fingerprint` all enumerate this table.
static EXPORT_TARGETS: &[ExportTarget] = &[
    ExportTarget {
        name: "Ragu.Instances.Point.AllocFp",
        fingerprint: fingerprint_instance::<PointAllocInstanceFp>,
    },
    ExportTarget {
        name: "Ragu.Instances.Point.AllocFq",
        fingerprint: fingerprint_instance::<PointAllocInstanceFq>,
    },
    ExportTarget {
        name: "Ragu.Instances.Point.Double",
        fingerprint: fingerprint_instance::<PointDoubleInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Point.DoubleAndAddIncomplete",
        fingerprint: fingerprint_instance::<PointDoubleAndAddIncompleteInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Point.AddIncomplete",
        fingerprint: fingerprint_instance::<PointAddIncompleteInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Point.ConditionalEndo",
        fingerprint: fingerprint_instance::<PointConditionalEndoInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Point.ConditionalNegate",
        fingerprint: fingerprint_instance::<PointConditionalNegateInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.Mul",
        fingerprint: fingerprint_instance::<ElementMulInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.Square",
        fingerprint: fingerprint_instance::<ElementSquareInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.Alloc",
        fingerprint: fingerprint_instance::<ElementAllocInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.AllocSquare",
        fingerprint: fingerprint_instance::<ElementAllocSquareInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.DivNonzero",
        fingerprint: fingerprint_instance::<ElementDivNonzeroInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.FoldN3",
        fingerprint: fingerprint_instance::<ElementFoldInstanceN3>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.FoldN7",
        fingerprint: fingerprint_instance::<ElementFoldInstanceN7>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.EnforceRootOfUnityK2",
        fingerprint: fingerprint_instance::<ElementEnforceRootOfUnityInstanceK2>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.EnforceRootOfUnityK5",
        fingerprint: fingerprint_instance::<ElementEnforceRootOfUnityInstanceK5>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.EnforceZero",
        fingerprint: fingerprint_instance::<ElementEnforceZeroInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.Invert",
        fingerprint: fingerprint_instance::<ElementInvertInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.InvertWith",
        fingerprint: fingerprint_instance::<ElementInvertWithInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.EnforceNonzero",
        fingerprint: fingerprint_instance::<ElementEnforceNonzeroInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.NonzeroBank.ScopeK2",
        fingerprint: fingerprint_instance::<NonzeroBankScopeInstanceK2>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.IsEqual",
        fingerprint: fingerprint_instance::<ElementIsEqualInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.IsZero",
        fingerprint: fingerprint_instance::<ElementIsZeroInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Core.Mul",
        fingerprint: fingerprint_instance::<CoreMulInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Boolean.Alloc",
        fingerprint: fingerprint_instance::<BooleanAllocInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Boolean.And",
        fingerprint: fingerprint_instance::<BooleanAndInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Boolean.ConditionalSelect",
        fingerprint: fingerprint_instance::<BooleanConditionalSelectInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Boolean.ConditionalEnforceEqual",
        fingerprint: fingerprint_instance::<BooleanConditionalEnforceEqualInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Endoscalar.Alloc",
        fingerprint: fingerprint_instance::<EndoscalarAllocInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Endoscalar.GroupScale",
        fingerprint: fingerprint_instance::<EndoscalarGroupScaleInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Endoscalar.Lift",
        fingerprint: fingerprint_instance::<EndoscalarLiftInstance>,
    },
];

fn default_autogen_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lean")
}

#[derive(Parser)]
#[command(name = "lean_extraction")]
#[command(about = "Export/check generated Lean files and fingerprint extracted circuit traces")]
struct Cli {
    #[command(subcommand)]
    command: Command,

    /// Root directory that contains the Lean source tree.
    #[arg(default_value_os_t = default_autogen_root())]
    autogen_root: PathBuf,
}

#[derive(Subcommand, Clone, Copy)]
enum Command {
    /// Write the generated Lean files (the instance import root and the
    /// fingerprint instance list) to disk.
    Export,
    /// Compare the generated Lean files with the files already on disk.
    Check,
    /// Print the canonical fingerprint digest of every exported instance.
    ///
    /// CI compares this output against the same digests computed in Lean from
    /// the Clean reimplementations.
    Fingerprint,
}

/// Monomorphized helper used by the static export target table.
fn fingerprint_instance<I: CircuitInstance>() -> String {
    I::fingerprint()
}

fn generated_instances_root(autogen_root: &Path) -> (PathBuf, String) {
    let path = autogen_root.join("Ragu/Instances.lean");
    let mut contents = EXPORT_TARGETS
        .iter()
        .map(|target| format!("import {}", target.name))
        .collect::<Vec<_>>()
        .join("\n");
    contents.push('\n');
    (path, contents)
}

/// Generated list pairing every formal instance with its module name, used by
/// the `fingerprints` executable on the Lean side.
fn generated_fingerprint_instances(autogen_root: &Path) -> (PathBuf, String) {
    let path = autogen_root.join("Ragu/Fingerprint/Instances.lean");
    let entries = EXPORT_TARGETS
        .iter()
        .map(|target| target.name)
        .map(|name| format!("  (\"{name}\", {name}.formal_instance)"))
        .collect::<Vec<_>>()
        .join(",\n");
    let contents = format!(
        "import Ragu.Fingerprint\nimport Ragu.Instances\n\nnamespace Ragu.Fingerprint\n\n\
         /-- Every exported circuit instance, paired with its Lean module name.\n\n\
         Autogenerated by `lean_extraction`; do not edit. Used by the `fingerprints`\n\
         executable, whose output CI compares against\n\
         `cargo run -p lean_extraction -- fingerprint`. -/\n\
         def instances : List (String × Ragu.Core.Statements.FormalInstance) := [\n{entries}\n]\n\n\
         end Ragu.Fingerprint\n"
    );
    (path, contents)
}

fn export_all(autogen_root: &Path) -> std::io::Result<()> {
    let (path, contents) = generated_instances_root(autogen_root);
    fs::write(&path, contents)?;
    println!("wrote Ragu.Instances to {}", path.display());

    let (path, contents) = generated_fingerprint_instances(autogen_root);
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(&path, contents)?;
    println!("wrote Ragu.Fingerprint.Instances to {}", path.display());

    Ok(())
}

/// Print `<module name> <digest>` for every exported instance.
fn fingerprint_all() {
    for target in EXPORT_TARGETS {
        println!("{} {}", target.name, (target.fingerprint)());
    }
}

fn check_file(
    name: &str,
    path: PathBuf,
    expected: String,
    mismatches: &mut usize,
) -> std::io::Result<()> {
    match fs::read_to_string(&path) {
        Ok(actual) if actual == expected => {
            println!("ok {name}");
        }
        Ok(_) => {
            eprintln!("mismatch {name} at {}", path.display());
            *mismatches += 1;
        }
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
            eprintln!("missing {name} at {}", path.display());
            *mismatches += 1;
        }
        Err(err) => return Err(err),
    }

    Ok(())
}

fn check_all(autogen_root: &Path) -> std::io::Result<bool> {
    let mut mismatches = 0;

    let (path, expected) = generated_instances_root(autogen_root);
    check_file("Ragu.Instances", path, expected, &mut mismatches)?;

    let (path, expected) = generated_fingerprint_instances(autogen_root);
    check_file(
        "Ragu.Fingerprint.Instances",
        path,
        expected,
        &mut mismatches,
    )?;

    if mismatches > 0 {
        eprintln!(
            "\n{mismatches} generated Lean file(s) out of date.\n\
             hint: run `cargo run -p lean_extraction -- export` and commit the result."
        );
    }

    Ok(mismatches == 0)
}

fn main() -> ExitCode {
    let cli = Cli::parse();

    let result = match cli.command {
        Command::Export => export_all(&cli.autogen_root).map(|_| ExitCode::SUCCESS),
        Command::Check => check_all(&cli.autogen_root).map(|ok| {
            if ok {
                ExitCode::SUCCESS
            } else {
                ExitCode::from(1)
            }
        }),
        Command::Fingerprint => {
            fingerprint_all();
            Ok(ExitCode::SUCCESS)
        }
    };

    match result {
        Ok(code) => code,
        Err(err) => {
            eprintln!("{err}");
            ExitCode::from(1)
        }
    }
}
