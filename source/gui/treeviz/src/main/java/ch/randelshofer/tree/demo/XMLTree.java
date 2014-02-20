/*
 * @(#)XMLTree.java  1.1  2011-01-20
 *
 * Copyright (c) 2007 Werner Randelshofer, Goldau, Switzerland.
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
import java.io.*;
import java.net.URL;
import java.util.Stack;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;
import javax.xml.parsers.*;
import org.xml.sax.*;
import org.xml.sax.helpers.DefaultHandler;

/**
 * XMLTree produces a general purpose tree over a XML file.
 * See {@link XMLNodeInfo} on how the XML data structure is being interpreted.
 *
 * @author  Werner Randelshofer
 * @version 1.1 2011-01-20 Adds network support.
 * <br>1.0 23. Juni 2008 Created.
 */
public class XMLTree implements DemoTree {

    private XMLNode root;
    private XMLNodeInfo info;
    private ProgressObserver p;

    public XMLTree(File xmlFile) throws IOException {
        FileInputStream in = new FileInputStream(xmlFile);
        try {
            read(in,xmlFile.getName(),xmlFile.length());
        } finally {
            in.close();
        }
    }
    public XMLTree(URL xmlFile) throws IOException {
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

    public void read(InputStream in, String rootName,long fileLength) throws IOException {    /** Creates a new instance. */
   
        p = null;
        if (p == null) {
            p = new ProgressView("Opening " + rootName, "", 0, 1);
            p.setIndeterminate(true);
        }
        try {
            root = new XMLNode();
            info = new XMLNodeInfo();

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

                saxParser.parse(sis, new DefaultHandler() {

                    private Stack<XMLNode> stack = new Stack<XMLNode>();

                    {
                        stack.push(root);
                    }

                    @Override
                    public void startElement(String uri, String localName,
                            String qName, Attributes attributes)
                            throws SAXException {
                        XMLNode node = new XMLNode();
                        node.setName(qName.intern());
                        for (int i = 0, n = attributes.getLength(); i < n; i++) {
                            // internalizing attribute names considerably saves memory
                            String name = attributes.getLocalName(i).intern();
                            node.putAttribute(name, attributes.getValue(i).intern());
                            //info.putAttribute(name,attributes.getValue(i));
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
                throw new IOException("XML Parser configuration error", ex);
            } catch (SAXException ex) {
                throw new IOException("XML Error", ex);
            } finally {
                
            }
            p.setNote("Calculating statistics");
            p.setIndeterminate(true);

            root = (XMLNode) root.children().get(0);

            info.init(root);
        } finally {
            p.close();
        }
    }

    @Override
    public XMLNode getRoot() {
        return root;
    }

    @Override
    public XMLNodeInfo getInfo() {
        return info;
    }
}
