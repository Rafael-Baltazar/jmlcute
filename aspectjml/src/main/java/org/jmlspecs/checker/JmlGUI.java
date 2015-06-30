// Generated from JmlGUI.gui
package org.jmlspecs.checker;

import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;

import javax.swing.JFileChooser;

import org.multijava.util.Options;
import org.multijava.util.gui.GUIOutputWindow;
import org.multijava.util.gui.GUIUtil;

/** This class is automatically generated from JmlGUI.gui
 *  and contains member fields corresponding to tool-specific GUI specifications.
 */
public class JmlGUI extends org.multijava.util.gui.GUI {


  public static void main(String[] args) {
    init(args, true);
  }


  public static JmlGUI init(String[] args, boolean standAlone) {
    JmlOptions options = new JmlOptions();
    ArrayList infiles = new ArrayList();
    ArrayList extraArguments = new ArrayList();
    boolean commandLine = false;
    if (args.length != 0) {
      commandLine = true;
      new Main().runParser(args, options, infiles);
    }
    return new JmlGUI(options, infiles, commandLine, standAlone);
  }


  public JmlGUI(Options options, ArrayList infiles, boolean commandLine, boolean standAlone) {
    super("Jml", options, infiles, commandLine, standAlone);
  }


  public void interruptCompilation() {
    Main.interruptCompilation();
  }


  protected boolean dirInClassPath(Options opt, String dir) {
    if (((JmlOptions)opt).sourcepath() != null) {
      return GUIUtil.dirInPath(((JmlOptions)opt).sourcepath(), dir);
    } else if (((JmlOptions)opt).classpath() != null) {
      return GUIUtil.dirInPath(((JmlOptions)opt).classpath(), dir);
    } else {
      return false;
    }
  }


  protected String getClasspath(Options opt) {
    return ((JmlOptions)opt).classpath();
  }


  protected String getSourcepath(Options opt) {
    return ((JmlOptions)opt).sourcepath();
  }


  protected OpenHandler createOpenHandlerInstance() {
    return new JmlOpenHandler();
  }


  protected Compilation createCompilationInstance(String[] files, Options opt, OutputStream os) {
    return new JmlCompilation(files, (JmlOptions)opt, os);
  }


  protected String getWebpageName() {
    return "JML Web Page";
  }


  protected String getWebpageLocation() {
    return "http://www.jmlspecs.org";
  }


  protected GUIOutputWindow createOutputWindow(InputStream is) {
    return new GUIOutputWindow(this, is);
  }


  protected class JmlOpenHandler extends OpenHandler {
    protected JmlOpenHandler() {
    }
    protected JFileChooser createFileChooser() {
      JFileChooser fileChooser = super.createFileChooser();
      AllFilesGUIFileFilter all = new AllFilesGUIFileFilter();
      fileChooser.addChoosableFileFilter(all);
      fileChooser.addChoosableFileFilter(new JmlGUIFileFilter(".jml"));
      fileChooser.addChoosableFileFilter(new JmlGUIFileFilter(".refines-jml"));
      fileChooser.addChoosableFileFilter(new JmlGUIFileFilter(".jml-refined"));
      fileChooser.addChoosableFileFilter(new JmlGUIFileFilter(".spec"));
      fileChooser.addChoosableFileFilter(new JmlGUIFileFilter(".refines-spec"));
      fileChooser.addChoosableFileFilter(new JmlGUIFileFilter(".spec-refined"));
      fileChooser.addChoosableFileFilter(new JmlGUIFileFilter(".java"));
      fileChooser.addChoosableFileFilter(new JmlGUIFileFilter(".refines-java"));
      fileChooser.addChoosableFileFilter(new JmlGUIFileFilter(".java-refined"));
      fileChooser.setFileFilter(all);
      return fileChooser;
    }
  }


  protected class AllFilesGUIFileFilter extends GUIFileFilter {
    public boolean hasActiveSuffix(String name) {
      return name.endsWith(".jml")
        || name.endsWith(".refines-jml")
        || name.endsWith(".jml-refined")
        || name.endsWith(".spec")
        || name.endsWith(".refines-spec")
        || name.endsWith(".spec-refined")
        || name.endsWith(".java")
        || name.endsWith(".refines-java")
        || name.endsWith(".java-refined");
    }
    public String getDescription() {
      return "JML Readable Files";
    }
  }


  protected class JmlGUIFileFilter extends GUIFileFilter {
    String suffix;
    public JmlGUIFileFilter(String suffix) {
      this.suffix = suffix;
    }
    public boolean hasActiveSuffix(String name) {
      return name.endsWith(suffix);
    }
    public String getDescription() {
      return suffix;
    }
  }


  protected class JmlCompilation extends Compilation implements Runnable {
    private String[] files;
    private JmlOptions options;
    private OutputStream os;

    protected JmlCompilation(String[] files, JmlOptions options, OutputStream os) {
      this.files = files;
      this.options = options;
      this.os = os;
    }

    public void run() {
      Main.compile(files, options, os);
    }
  }


}
