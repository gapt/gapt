package gapt.prooftool

import java.awt.Color
import java.awt.Font._
import java.awt.image.BufferedImage
import java.io.File

import os.{Path, write}
import javax.imageio.ImageIO
import javax.swing.WindowConstants
import javax.swing.filechooser.FileFilter
import com.itextpdf.awt.PdfGraphics2D

import scala.swing.Dialog.Message
import scala.swing.Swing.EmptyIcon
import scala.swing._
import scala.swing.event.Key

/**
 * The main window of the ProofTool application.
 *
 * @param name The name to be displayed at the top.
 * @param content The object to be displayed.
 * @tparam T The type of content.
 */
abstract class ProofToolViewer[+T](val name: String, val content: T) extends Reactor {
  type MainComponentType <: Component // The type of the mainComponent object (e.g., DrawSequentProof in the case of LK proofs).
  protected val nLine = sys.props("line.separator")
  val dnLine = nLine + nLine
  var DEBUG = false

  // Font
  val defaultFontSize = 12
  private var currentFontSize_ = defaultFontSize
  def currentFontSize = currentFontSize_
  def currentFontSize_=(sz: Int) = {
    currentFontSize_ = sz
    font = new Font(SANS_SERIF, PLAIN, sz)
  }
  private var font_ = new Font(SANS_SERIF, PLAIN, currentFontSize)
  def font = font_
  def font_=(ft: Font) = {
    font_ = ft
    publisher.publish(FontChanged)
    mainComponent.revalidate()
  }
  var launcher_history = List[(String, AnyRef, Int)]()
  val publisher = new ProofToolPublisher

  val mBar = new MenuBar {
    focusable = true

    contents += new Menu("File") {
      mnemonic = Key.F
      contents ++= fileMenuContents
    }

    contents += new Menu("View") {
      mnemonic = Key.V
      contents ++= viewMenuContents
    }
  }

  def showFrame(): Unit = {
    top.preferredSize = new Dimension(700, 500)
    top.pack()
    top.centerOnScreen()
    top.open()
    top.maximize()
  }

  lazy val top = new Frame {
    title = "ProofTool"
    menuBar = mBar
    contents = new BorderPanel
    peer setDefaultCloseOperation WindowConstants.DISPOSE_ON_CLOSE
  }

  val mainComponent = createMainComponent

  protected var contentPanel_ = new PTContentPanel(this, name, mainComponent)
  def contentPanel = contentPanel_
  def contentPanel_=(p: PTContentPanel) = {
    contentPanel_ = p
    top.contents = mainPanel
  }

  def mainPanel: Component = contentPanel

  top.contents = mainPanel

  // Function that creates the main component from the content object, e.g., put an LKProof in a DrawSequentProof object.
  // Subclasses need to implement this!
  def createMainComponent: MainComponentType

  /**
   * Resizes the content to a new font size.
   *
   * @param fSize The new font size.
   */
  def resizeContent(fSize: Int): Unit = {
    mainPanel.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    currentFontSize = fSize
    mainPanel.cursor = java.awt.Cursor.getDefaultCursor
  }

  /**
   * Opens a proof db and displays all its contents.
   */
  def fOpen(): Unit = {
    val chooser = createChooser(".gz", ".ivy", ".lks", ".lksc", ".llk", ".pdf", ".png", ".rs", ".tex", ".tptp", ".xml")
    chooser.showOpenDialog(mBar) match {
      case FileChooser.Result.Approve =>
        mainPanel.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
        val parser = new FileParser(this)
        parser.parseFile(chooser.selectedFile.getPath)
        for ((name, p) <- parser.getProofs) prooftool(p, name)
        for ((name, p) <- parser.getResolutionProofs) prooftool(p, name)

        mainPanel.cursor = java.awt.Cursor.getDefaultCursor
      case _ =>
    }
  }

  /**
   * Exports a component as a pdf.
   *
   * @param component The component to be exported.
   */
  def fExportPdf(component: Component): Unit = {
    val chooser = createChooser(".pdf")
    chooser.showSaveDialog(mBar) match {
      case FileChooser.Result.Approve =>
        try {
          mainPanel.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
          import java.io.FileOutputStream

          import com.itextpdf.text.pdf.PdfWriter
          import com.itextpdf.text.{Document, Rectangle => PdfRectangle}

          val width = component.size.width
          val height = component.size.height
          val document = new Document(new PdfRectangle(width.toFloat, height.toFloat + 20.0f))
          val result = chooser.selectedFile.getPath
          val path = if (result.endsWith(".pdf")) result else result + ".pdf"
          val writer = PdfWriter.getInstance(document, new FileOutputStream(path))
          document.open()
          val content = writer.getDirectContent
          val template = content.createTemplate(width.toFloat, height.toFloat)
          val g2 = new PdfGraphics2D(template, width.toFloat, height.toFloat, true)
          component.paint(g2)
          g2.dispose()
          content.addTemplate(template, 0, 10)
          document.close()
        } catch {
          case e: Throwable => errorMessage("Can't export to pdf! " + dnLine + getExceptionString(e))
        } finally { mainPanel.cursor = java.awt.Cursor.getDefaultCursor }
      case _ =>
    }
  }

  /**
   * Exports a component as a PNG.
   *
   * @param component The component to be exported.
   */
  def fExportPng(component: Component): Unit = {
    val chooser = createChooser(".png")
    chooser.showSaveDialog(mBar) match {
      case FileChooser.Result.Approve =>
        try {
          mainPanel.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)

          val width = component.size.width
          val height = component.size.height
          val img = new BufferedImage(width, height, BufferedImage.TYPE_INT_RGB)
          val g = img.createGraphics()
          g.setBackground(new Color(255, 255, 255))
          g.fillRect(0, 0, width, height)
          component.paint(g)
          val result = chooser.selectedFile.getPath
          val path = if (result.endsWith(".png")) result else result + ".png"
          ImageIO.write(img, "png", new File(path))
        } catch {
          case e: Throwable => errorMessage("Can't export to png! " + dnLine + getExceptionString(e))
        } finally { mainPanel.cursor = java.awt.Cursor.getDefaultCursor }
      case _ =>
    }
  }

  /**
   * Zooms in by multiplying font size by 3/2.
   */
  def increaseFontSize(): Unit = {
    currentFontSize * 3 / 2 match {
      case j: Int if j > 72 =>
      case j: Int =>
        resizeContent(j)
    }
  }

  /**
   * Zooms out by multiplying font size by 2/3.
   */
  def decreaseFontSize(): Unit = {
    currentFontSize / 3 * 2 match {
      case j: Int if j < 1 =>
      case j: Int =>
        resizeContent(j)
    }
  }

  def inputMessage(message: String, values: Seq[String]) =
    Dialog.showInput[String](mainPanel, message, "ProofTool Input", Dialog.Message.Plain, EmptyIcon, values, if (values.isEmpty) "" else values.head)

  /**
   * Displays an info message.
   *
   * @param info The text of the message.
   */
  def infoMessage(info: String): Unit = {
    Dialog.showMessage(mainPanel, info, "ProofTool Information")
  }

  /**
   * Displays a warning message.
   *
   * @param warning The text of the message.
   */
  def warningMessage(warning: String): Unit = {
    Dialog.showMessage(mainPanel, warning, "ProofTool Warning", Dialog.Message.Warning)
  }

  /**
   * Displays an error message.
   *
   * @param error The text of the message.
   */
  def errorMessage(error: String): Unit = {
    Dialog.showMessage(mainPanel, error, "ProofTool Error", Dialog.Message.Error)
  }

  /**
   * Displays a question.
   *
   * @param question The text of the question.
   */
  def questionMessage(question: String) =
    Dialog.showConfirmation(mainPanel, question, "ProofTool Question", Dialog.Options.YesNo, Message.Question)

  def getExceptionString(e: Throwable): String = {
    val st = e.toString.replaceAll(",", "," + nLine) + nLine
    val trace = e.getStackTrace
    if (trace.length > 10)
      Range(0, 10).map(i => trace.apply(i)).foldLeft(st)((s, x) => s + nLine + "   at " + x.toString) + nLine + "   ......."
    else e.getStackTrace.toString
  }

  protected def createChooser(extensions: String*): FileChooser = new FileChooser {
    extensions.foreach(fe =>
      peer.addChoosableFileFilter(
        new FileFilter {
          def accept(f: File): Boolean = {
            if (f.getName.endsWith(fe) || f.isDirectory) true
            else false
          }
          def getDescription = fe
        }
      )
    )

    fileFilter = acceptAllFileFilter
  }

  // Menus and menu items

  protected def openButton = MenuButtons.openButton(this)

  protected def exportToPDFButton = MenuButtons.exportToPDFButton(this)

  protected def exportToPNGButton = MenuButtons.exportToPNGButton(this)

  protected def zoomInButton = MenuButtons.increaseFontSizeButton(this)

  protected def zoomOutButton = MenuButtons.decreaseFontSizeButton(this)

  protected def showDebugBordersButton = MenuButtons.ShowDebugBordersButton(this)

  /**
   *
   * @return The contents of the "File" menu.
   */
  def fileMenuContents: Seq[Component] = Seq(openButton, new Separator, exportToPDFButton, exportToPNGButton)

  /**
   *
   * @return The contents of the "View" menu.
   */
  def viewMenuContents: Seq[Component] = Seq(zoomInButton, zoomOutButton)

  /**
   * @return The contents of the "Debug" menu.
   */
  def debugMenuContents: Seq[Component] = Seq(showDebugBordersButton)
}

/**
 * A Prooftool window where the main component is contained in a ScrollPane.
 * @param name The name to be displayed at the top.
 * @param content The object to be displayed.
 * @tparam T The type of content.
 */
abstract class ScrollableProofToolViewer[+T](name: String, content: T) extends ProofToolViewer(name, content) {

  lazy val scrollPane = new PTScrollPane
  scrollPane.contentPanel = contentPanel

  override def contentPanel_=(p: PTContentPanel) = {
    contentPanel_ = p
    scrollPane.contentPanel = p
  }

  override def mainPanel = scrollPane
}

/**
 * A trait for ProofToolViewer objects that can save their contents.
 * @tparam T The type of the content object.
 */
trait Savable[T] extends ProofToolViewer[T] {

  /**
   * Saves an object to disk.
   * @param name
   * @param obj The object to be saved.
   */
  def fSave(name: String, obj: T): Unit = {
    val chooser = createChooser(saveFormats.keys.toList: _*)
    chooser.showSaveDialog(mBar) match {
      case FileChooser.Result.Approve =>
        mainPanel.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
        val result = chooser.selectedFile.getAbsolutePath
        try {
          saveFormats.toList.collectFirst {
            case (format, exporter) if result.endsWith(format) || chooser.fileFilter.getDescription == format =>
              val fileName = if (result.endsWith(format)) result else result + format
              (fileName, exporter(obj))
          } match {
            case Some((fileName, content)) => write(Path(fileName), content)
            case None                      => infoMessage("Content cannot be saved in this format.")
          }
        } catch { case e: Throwable => errorMessage("Cannot save the proof! " + dnLine + getExceptionString(e)) }
        finally { mainPanel.cursor = java.awt.Cursor.getDefaultCursor }
      case _ =>
    }
  }

  def saveFormats: Map[String, T => String]

  private def saveAsButton = MenuButtons.saveAsButton(this)
  override def fileMenuContents = Seq(openButton, saveAsButton, new Separator, exportToPDFButton, exportToPNGButton)
}
