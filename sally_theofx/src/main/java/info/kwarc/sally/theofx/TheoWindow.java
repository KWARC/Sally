package info.kwarc.sally.theofx;

import static javafx.concurrent.Worker.State.FAILED;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.awt.event.WindowListener;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URI;
import java.net.URL;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

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

public class TheoWindow implements Runnable {

	private int sizeY;
	private int sizeX;
	private String webColor = "#666970";
	private int posX;
	private int posY;
	private String stageTitle = "Theo";
	private JFXPanel jfxPanel;
	private WebEngine engine;
	private String url;
	private JFrame frame = new JFrame();
	private JPanel panel = new JPanel(new BorderLayout());
	private boolean visible;
	private String initCookies;

	public TheoWindow(int sizeX, int sizeY, int posX,
			int posY, String stageTitle, String url, String cookies, boolean visible) {
		super();
		this.sizeY = sizeY;
		this.sizeX = sizeX;
		this.posX = posX;
		this.posY = posY;
		this.stageTitle = stageTitle;
		this.url = url;
		this.visible = visible;
		this.initCookies = cookies;
	}

	public static TheoWindow addWindow(Integer sizeY, Integer sizeX,
			Integer posX, Integer posY, String stageTitle, String url, String cookies, boolean visible){
		TheoWindow simple;
		SwingUtilities.invokeLater(simple=new TheoWindow(sizeX, sizeY , posX, posY, stageTitle, url, cookies, visible));
		return simple;
	}
	
	
	// private JLabel lblStatus = new JLabel();

	// private JButton btnGo = new JButton("Go"); //Butonul cu Go din dreapta,
	// inutil dar interesant pentru reload
	// private JTextField txtURL = new JTextField();
	private JProgressBar progressBar = new JProgressBar();

	WindowListener exitListener = new WindowAdapter() {

		@Override
		public void windowClosing(WindowEvent e) {
			System.out.println("window closed");

		}
	};

	/**
	 * Class for allowing interaction from javascript
	 * @author Alex
	 *
	 */
	private class JavaApp {

		public void openNewWindow(int sizeX, int sizeY, int posX,
				int posY, String stageTitle, String url, String cookies, boolean visible) {
			addWindow(sizeX, sizeY , posX, posY, "Theo", url, cookies, visible);
		}
	}

	private void initComponents() {
		jfxPanel = new JFXPanel();

		createScene();

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

		panel.add(topBar, BorderLayout.NORTH);
		panel.add(jfxPanel, BorderLayout.CENTER);
		panel.add(statusBar, BorderLayout.SOUTH);

		frame.getContentPane().add(panel);
		frame.addWindowListener(exitListener);
	}

	private void createScene() {

		Platform.runLater(new Runnable() {

			public void run() {

				WebView view = new WebView();
				engine = view.getEngine();
				URI uri = URI.create(url);
				Map<String, List<String>> headers = new LinkedHashMap<String, List<String>>();
				headers.put("Set-Cookie", Arrays.asList(initCookies));
				try {
					java.net.CookieHandler.getDefault().put(uri, headers);
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}

				/*
				 * engine.titleProperty().addListener(new
				 * ChangeListener<String>() {
				 * 
				 * @Override public void changed(ObservableValue<? extends
				 * String> observable, String oldValue, final String newValue) {
				 * SwingUtilities.invokeLater(new Runnable() {
				 * 
				 * @Override public void run() { frame.setTitle(newValue); } });
				 * } });
				 * 
				 * engine.setOnStatusChanged(new
				 * EventHandler<WebEvent<String>>() {
				 * 
				 * @Override public void handle(final WebEvent<String> event) {
				 * SwingUtilities.invokeLater(new Runnable() {
				 * 
				 * @Override public void run() {
				 * lblStatus.setText(event.getData()); } }); } });
				 * 
				 * engine.locationProperty().addListener(new
				 * ChangeListener<String>() {
				 * 
				 * @Override public void changed(ObservableValue<? extends
				 * String> ov, String oldValue, final String newValue) {
				 * SwingUtilities.invokeLater(new Runnable() {
				 * 
				 * @Override public void run() { txtURL.setText(newValue); } });
				 * } });
				 */

				engine.getLoadWorker().stateProperty()
						.addListener(new ChangeListener<State>() {

							public void changed(
									ObservableValue<? extends State> ov,
									State oldState, State newState) {

								if (newState == State.SUCCEEDED) {
									JSObject win = (JSObject) engine
											.executeScript("window");
									win.setMember("app", new JavaApp());
								}
							}
						});

				engine.getLoadWorker().workDoneProperty()
						.addListener(new ChangeListener<Number>() {

							public void changed(
									ObservableValue<? extends Number> observableValue,
									Number oldValue, final Number newValue) {
								SwingUtilities.invokeLater(new Runnable() {

									public void run() {
										progressBar.setValue(newValue
												.intValue());
									}
								});
							}
						});

				engine.getLoadWorker().exceptionProperty()
						.addListener(new ChangeListener<Throwable>() {

							public void changed(
									ObservableValue<? extends Throwable> o,
									Throwable old, final Throwable value) {
								if (engine.getLoadWorker().getState() == FAILED) {
									SwingUtilities.invokeLater(new Runnable() {

										public void run() {
											JOptionPane
													.showMessageDialog(
															panel,
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

	private static String toURL(String str) {
		try {
			return new URL(str).toExternalForm();
		} catch (MalformedURLException exception) {
			return null;
		}
	}

	public void run() {
		
		frame.setBounds(posX, posY, sizeX, sizeY);
		//frame.setPreferredSize(new Dimension(sizeX, sizeY));
		// frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

		initComponents();

		loadURL(this.url);

		//frame.pack();
		frame.setVisible(visible);
		
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
			Platform.runLater(new Runnable() {
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

}
