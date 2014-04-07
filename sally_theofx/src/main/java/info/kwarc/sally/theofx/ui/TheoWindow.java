package info.kwarc.sally.theofx.ui;

import static javafx.concurrent.Worker.State.FAILED;
import info.kwarc.sally.theofx.interfaces.ITheoAppProvider;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.net.MalformedURLException;
import java.net.URI;
import java.net.URL;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import javafx.application.Platform;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.concurrent.Worker.State;
import javafx.embed.swing.JFXPanel;
import javafx.scene.Scene;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;

import javax.swing.BorderFactory;
import javax.swing.JFrame;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JProgressBar;
import javax.swing.SwingUtilities;

import netscape.javascript.JSObject;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import Sally.Cookie;

import com.google.inject.Inject;
import com.google.inject.assistedinject.Assisted;

public class TheoWindow implements Runnable {

	private static Random rand = new Random();
	
	private Long processInstanceID;
	private Logger loggr;
	private int wndID;
	private int sizeY;
	private int sizeX;
	//private String webColor = "#666970";
	private int posX;
	private int posY;
	private String stageTitle;
	private JFXPanel jfxPanel;
	private WebEngine engine;
	private String url;
	private JFrame frame = new JFrame();
	private JPanel panel = new JPanel(new BorderLayout());
	private boolean visible;
	private Cookie initCookies;
	ITheoAppProvider appProvider;

	@Inject
	public TheoWindow(@Assisted("pid") Long pid, @Assisted("sizeX")  int sizeX, @Assisted("sizeY") int sizeY, @Assisted("posX") int posX,
			@Assisted("posY") int posY, @Assisted("stageTitle") String stageTitle, @Assisted("url") String url, @Assisted Cookie cookies, @Assisted boolean visible, ITheoAppProvider appProvider) {
		super();
		this.appProvider = appProvider;
		this.processInstanceID = pid ;
		this.sizeY = sizeY;
		this.sizeX = sizeX;
		this.posX = posX;
		this.posY = posY;
		this.stageTitle = stageTitle;
		this.url = url;
		this.visible = visible;
		this.initCookies = cookies;
		this.wndID = rand.nextInt();
		this.loggr = LoggerFactory.getLogger(TheoWindow.class);
	}

	public void showWindow() {
		try {
			SwingUtilities.invokeAndWait(this);
		} catch (InvocationTargetException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	public int getWndID() {
		return wndID;
	}


	public void closeWindow() {
		frame.setVisible(false);
		frame.dispose();
	}

	private JProgressBar progressBar = new JProgressBar();
	//private ToggleGroup groupV = new ToggleGroup();

	private void initComponents() {
		jfxPanel = new JFXPanel();


		requestCreateScene();

		/*
		 * ActionListener al = new ActionListener() {
		 * 
		 * @Override public void actionPerformed(ActionEvent e) {
		 * loadURL(txtURL.getText()); } };
		 */
		// btnGo.addActionListener(al);
		// txtURL.addActionListener(al);

		progressBar.setPreferredSize(new Dimension(150, 18));
		progressBar.setStringPainted(true);

		JPanel topBar = new JPanel(new BorderLayout(5, 0));
		topBar.setBorder(BorderFactory.createEmptyBorder(3, 5, 3, 5));
		// topBar.add(txtURL, BorderLayout.CENTER);
		// topBar.add(btnGo, BorderLayout.EAST);

		JPanel statusBar = new JPanel(new BorderLayout(5, 0));
		statusBar.setBorder(BorderFactory.createEmptyBorder(3, 5, 3, 5));
		// statusBar.add(lblStatus, BorderLayout.CENTER);
		statusBar.add(progressBar, BorderLayout.EAST);

		/*		tb1.setToggleGroup(groupV);
		tb1.setSelected(true);
		tb2.setToggleGroup(groupV);
		tb3.setToggleGroup(groupV);*/


		//panel.add(groupV, BorderLayout.WEST);

		panel.add(topBar, BorderLayout.NORTH);
		panel.add(jfxPanel, BorderLayout.CENTER);
		panel.add(statusBar, BorderLayout.SOUTH);

		frame.getContentPane().add(panel);
		//frame.addWindowListener(exitListener);
	}

	public void setCookie(String url, String cookies) {
		URI uri = URI.create(url);
		Map<String, List<String>> headers = new LinkedHashMap<String, List<String>>();
		headers.put("Set-Cookie", Arrays.asList(cookies));
		try {
			java.net.CookieHandler.getDefault().put(uri, headers);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	public void requestCreateScene(){
		{

			Platform.runLater(new Runnable() {

				public void run() {

					WebView view = new WebView();
					engine = view.getEngine();

					if (initCookies != null) {
						URI uri = URI.create(initCookies.getUrl());
						Map<String, List<String>> headers = new LinkedHashMap<String, List<String>>();
						headers.put("Set-Cookie", Arrays.asList(initCookies.getCookie()));
						try {
							java.net.CookieHandler.getDefault().put(uri, headers);
						} catch (IOException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
					}

					engine.getLoadWorker().stateProperty().addListener(new ChangeListener<State>() {
						public void changed(ObservableValue<? extends State> ov, State oldState, State newState) {
							if (newState == State.SUCCEEDED) {
								JSObject win = (JSObject) engine.executeScript("window");
								loggr.info(win.toString()+" "+ this.getClass().toString());
								//TODO change this int or add a new constructor
								win.setMember("app", appProvider.create(processInstanceID, engine));
								loggr.info("New TheoApp added.");
							}
							org.w3c.dom.html.HTMLElement q;
						}
					});

					engine.getLoadWorker().workDoneProperty().addListener(new ChangeListener<Number>() {
						public void changed(ObservableValue<? extends Number> observableValue, Number oldValue, 
								final Number newValue) { 
							SwingUtilities.invokeLater(new Runnable() {
								public void run() {
									progressBar.setValue(newValue.intValue());
								}
							});
						}
					});

					engine.getLoadWorker().exceptionProperty().addListener(new ChangeListener<Throwable>() {
						public void changed(
								ObservableValue<? extends Throwable> o,
								Throwable old, final Throwable value) {
							if (engine.getLoadWorker().getState() == FAILED) {
								SwingUtilities.invokeLater(new Runnable() {
									public void run() {
										JOptionPane.showMessageDialog( panel,
												(value != null) ? engine
														.getLocation()
														+ "\n"
														+ value.getMessage()
														: engine.getLocation()
														+ "\nUnexpected error.",
														"Loading error...",
														JOptionPane.ERROR_MESSAGE);
									}
								});
							}
						}
					});

					jfxPanel.setScene(new Scene(view));



				}
			});
		}

	} 


	public void loadURL(final String url) {
		Platform.runLater(new Runnable() {

			public void run() {
				String tmp = toURL(url);

				if (tmp == null) {
					tmp = toURL("http://" + url);
				}

				engine.load(tmp);
			}
		});
	}

	private String toURL(String str) {
		try {
			return new URL(str).toExternalForm();
		} catch (MalformedURLException exception) {
			return null;
		}
	}

	//@Override
	public void run() {

		frame.setBounds(posX, posY, sizeX, sizeY);
		//frame.setPreferredSize(new Dimension(sizeX, sizeY));
		// frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		initComponents();

		loadURL(this.url);

		//frame.pack();
		//JFrame.setDefaultLookAndFeelDecorated(true);

		//frame.setUndecorated(true);
		//frame.getRootPane().setWindowDecorationStyle(JRootPane.INFORMATION_DIALOG);
		frame.setVisible(visible);
		frame.setTitle(this.stageTitle);
		frame.setAlwaysOnTop(true);
	}

	public WebEngine getEngine() {
		return engine;
	}

	/**
	 * This is a safe method for changing the displayed URL. It is loadURL but
	 * with a try catch block.
	 * 
	 * @param url
	 */
	public void changeURL(final String url) {
		try {
			SwingUtilities.invokeLater(new Runnable() {
				public void run() {
					String tmp = toURL(url);

					tmp = toURL("http://" + url);
					engine.load(tmp);

				}
			});
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	public void resizeAndMove( int x, int y, int width, int height) {
		frame.setBounds(x, y, width, height);
	}


	public Long getPID() {
		return this.processInstanceID;
	}
}

/*	public static void initiateTestTheo(){
	//TheoWindow simple;
	addCommunicationWindow();
	addWindow(200, 200, 200, 200, "bla", "http://trac.kwarc.info", null, true);
	//initiated = true;
}*/
