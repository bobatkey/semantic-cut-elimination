use feature 'unicode_strings';
use utf8;

# Set Evince as the default PDF previewer
# $pdf_previewer = 'evince %S';

# Set Skim as the default PDF previewer
# $pdf_previewer = 'open -a Skim %S';

# Set Agda as the preprocessor
add_cus_dep('lagda.tex', 'tex', 0, 'run_agda');
sub run_agda {
  use File::Spec;

  my $base = shift @_;

  # Determine the LaTeX directory
  my ($base_volume, $base_directories, $base_file) = File::Spec->splitpath($base);
  my @agda_version_parts = split(/-/, `agda --numeric-version`);
  my $agda_version = $agda_version_parts[0];
  my $latex_dir = File::Spec->catfile("_build", $agda_version, "latex", $base_directories);
  print "LaTeX directory: $latex_dir\n";

  # Run Agda LaTeX backend
  my $ret = system('agda', '--latex', "--latex-dir=$latex_dir", "$base.lagda.tex");

  # Read the generated LaTeX file from the LaTeX directory
  my $temp_file = File::Spec->catfile($latex_dir, "$base_file.tex");
  open (my $temp_handle, '<', $temp_file) or die "Could not open $temp_file: $!";
  my $temp_contents = join("", <$temp_handle>);
  close ($temp_handle) or die "Could not close $temp_file: $!";

  # Rewrite `α ⁺` to `α⁺`
  # print $temp_contents;
  $temp_contents =~ s|
    \\AgdaBound\{A\}\\AgdaSpace\{\}%
    |
    \\AgdaBound\{A\}%
    |gx;
  $temp_contents =~ s|
    \\AgdaGeneralizable\{A\}\\AgdaSpace\{\}%
    |
    \\AgdaGeneralizable\{A\}%
    |gx;

  # Write the generated LaTeX file to the build directory
  my $out_file = "$base.tex";
  open (my $out_handle, '>', $out_file) or die "Could not open $out_file: $!";
  print $out_handle $temp_contents;
  close ($out_handle) or die "Could not close $out_file: $!";
  return $ret;
}
