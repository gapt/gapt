/*
 * @(#)TreevizFileSystemXMLNode.java  1.1  2011-01-20
 *
 * Copyright (c) 2007-2011 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.tree.demo;

import ch.randelshofer.gui.ProgressObserver;
import ch.randelshofer.gui.ProgressView;
import ch.randelshofer.io.*;
import ch.randelshofer.tree.TreeNode;
import java.io.*;
import java.net.URL;
import java.nio.charset.Charset;
import java.nio.charset.CharsetDecoder;
import java.nio.charset.CodingErrorAction;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Stack;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;
import javax.xml.parsers.*;
import org.xml.sax.*;
import org.xml.sax.helpers.DefaultHandler;

/**
 * TreevizFileSystemXMLTree reads an XML file with the root element named 
 * TreevizFileSystem and the top-level child elements Users and Files.
 * <p>
 * The children of the Users element are interpreted as user account data.
 * Each element should have the following attributes: id(XML-ID), name(Text), 
 * created(ISO-Date), isActive(boolean).<br>
 * Nesting of elements is not allowed. Other than that, there are no
 * more restrictions on the elements.
 * <p>
 * The children of the Files element are interpreted as a directory tree.
 * Each element should have the following attributes: name(Text), 
 * created(ISO-Date), size(Number), and "ownerRef"(id of a user), "creatorRef".
 * Nesting of elements is allowed to form a directory structure. Other than that,
 * there are no more restrictions on the elements.
 * 
 * 
 * See {@link XMLNodeInfo} on how the XML data structure is being interpreted.
 *
 * @author  Werner Randelshofer
 * @version 1.1 2011-01-20 Adds network support.
 * <br>1.0 25. Juni 2008 Created.
 */
public class TreevizFileSystemXMLTree implements DemoTree {

    private TreevizFileSystemXMLNode root;
    private TreevizFileSystemXMLNode filesRoot;
    private TreevizFileSystemXMLNode usersRoot;
    private TreevizFileSystemXMLNodeInfo info;
    ProgressObserver p;

    public TreevizFileSystemXMLTree(File xmlFile) throws IOException {
        FileInputStream in = new FileInputStream(xmlFile);
        try {
            read(in,xmlFile.getName(),xmlFile.length());
        } finally {
            in.close();
        }
    }
    public TreevizFileSystemXMLTree(URL xmlFile) throws IOException {
        InputStream in = xmlFile.openStream();
        try {
            String name=xmlFile.getPath();
            int p=name.lastIndexOf('/');
            if (p!=-1) {
                name=name.substring(p+1);
            }

            read(in, name, -1);
        } finally {
            in.close();
        }
    }

    public void read(InputStream in, String rootName,long fileLength) throws IOException {
        p = null;
        if (p == null) {
            p = new ProgressView("Opening " + rootName, "", 0, 1);
            p.setIndeterminate(true);
        }
        try {
            root = new TreevizFileSystemXMLNode();
            info = new TreevizFileSystemXMLNodeInfo(this);

            SAXParserFactory factory = SAXParserFactory.newInstance();
            try {
                SAXParser saxParser = factory.newSAXParser();
                BoundedRangeInputStream bris;
                if (rootName.endsWith(".zip")) {
                    bris = null;
                    ZipInputStream zis = new ZipInputStream(in);
                    for (ZipEntry entry = zis.getNextEntry(); entry != null; entry = zis.getNextEntry()) {
                        if (!entry.isDirectory() && entry.getName().endsWith(".xml")) {
                            bris = new BoundedRangeInputStream(zis);
                            if (entry.getSize() != -1) {
                                bris.setMaximum((int) entry.getSize() + 1);
                            }
                            break;
                        }
                    }
                    if (bris == null) {
                        throw new IOException("No XML file found inside of " + rootName + ".");
                    }

                } else {
                    bris = new BoundedRangeInputStream(in);
                    bris.setMaximum(fileLength==-1?Integer.MAX_VALUE:(int) fileLength + 1);
                }

                final SuspendableInputStream sis = new SuspendableInputStream(bris);
                p.setModel(bris);
                p.setIndeterminate(false);
                p.setDoCancel(new Runnable() {

                    @Override
                    public void run() {
                        sis.abort();
                    }
                });
                // Create an error resilient charset decoder for UTF-8
                Charset cs = Charset.forName("UTF-8");
                CharsetDecoder decoder = cs.newDecoder();
                decoder.onMalformedInput(CodingErrorAction.REPLACE);
                InputStreamReader isr = new InputStreamReader(sis, decoder);

//            saxParser.parse( new InputSource(new InputStreamReader(sis,"UTF-8")), new DefaultHandler() {
//            saxParser.parse(sis, new DefaultHandler() {
                saxParser.parse(new InputSource(isr), new DefaultHandler() {

                    private boolean isFirstElement = true;
                    private Stack<TreevizFileSystemXMLNode> stack = new Stack<TreevizFileSystemXMLNode>();


                    {
                        stack.push(root);
                    }

                    @Override
                    public void startElement(String uri, String localName,
                            String qName, Attributes attributes)
                            throws SAXException {
                        if (isFirstElement) {
                            isFirstElement = false;
                            if (!qName.equals("TreevizFileSystem")) {
                                throw new SAXException("Illegal root element: \"" + qName + "\" must be \"TreevizFileSystem\"");
                            }
                        }

                        TreevizFileSystemXMLNode node = new TreevizFileSystemXMLNode();
                        node.setName(qName.intern());
                        for (int i = 0, n = attributes.getLength(); i < n; i++) {
                            // internalizing attribute names considerably saves memory
                            String name = attributes.getQName(i).intern();
                            //     node.putAttribute(name, attributes.getValue(i).intern());
                            node.putAttribute(name, attributes.getValue(i));
                        }

                        stack.peek().addChild(node);
                        stack.push(node);
                    }

                    @Override
                    public void endElement(String uri, String localName, String qName)
                            throws SAXException {
                        stack.pop();
                    }
                });
            } catch (ParserConfigurationException ex) {
                IOException iex = new IOException("XML Parser configuration error");
                iex.initCause(ex);
                throw iex;
            } catch (SAXException ex) {
                IOException iex = new IOException("XML Error");
                iex.initCause(ex);
                throw iex;
            } finally {
                //
            }

            // the first child of the root must be named Users the second one named Files
            if (root.children().size() != 1) {
                throw new IOException("XML File is empty");
            }

            TreeNode rootElement = root.children().get(0);
            if (rootElement.children().size() != 2) {
                throw new IOException("TreevizFileSystem element must have two children");
            }
            usersRoot = (TreevizFileSystemXMLNode) rootElement.children().get(0);
            if (!usersRoot.getName().equals("Users")) {
                throw new IOException("First child of TreevizFileSystem element \"" + usersRoot.getName() + "\" must be named \"Users\"");
            }
            filesRoot = (TreevizFileSystemXMLNode) rootElement.children().get(1);
            if (!filesRoot.getName().equals("Files")) {
                throw new IOException("Second child of TreevizFileSystem element \"" + filesRoot.getName() + "\" must be named \"Files\"");
            }
        } finally {
            p.close();
        }

    }

    public TreevizFileSystemXMLNode getRoot() {
        return filesRoot;
    }

    public TreevizFileSystemXMLNode getUsersRoot() {
        return usersRoot;
    }

    public TreevizFileSystemXMLNodeInfo getInfo() {
        return info;
    }
}
