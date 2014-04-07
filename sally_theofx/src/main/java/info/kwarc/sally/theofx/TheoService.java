package info.kwarc.sally.theofx;

import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.doc.DocumentInformation;
import info.kwarc.sally.core.interaction.CallbackManager;
import info.kwarc.sally.core.interaction.IMessageCallback;
import info.kwarc.sally.core.theo.CookieProvider;
import info.kwarc.sally.core.theo.Coordinates;
import info.kwarc.sally.core.theo.ScreenCoordinatesProvider;
import info.kwarc.sally.core.theo.Theo;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.theofx.interfaces.ITheoWindowProvider;
import info.kwarc.sally.theofx.ui.TheoWindow;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import javax.swing.AbstractButton;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;

import Sally.Cookie;
import Sally.SallyFrameChoice;

import com.google.inject.Inject;
import com.google.inject.Singleton;
import com.google.protobuf.AbstractMessage;

@Singleton
public class TheoService implements Theo {

	SallyMenuItem chosenItem;
	HashMap<Integer, TheoWindow> openedWindows;
	ScreenCoordinatesProvider coordProvider;
	CookieProvider cookieProvider;
	ISallyWorkflowManager kb;
	ITheoWindowProvider theoWindowProvider;
	CallbackManager callbacks;
	
	@Inject
	public TheoService(ScreenCoordinatesProvider coordProvider, CookieProvider cookieProvider, ISallyWorkflowManager kb, ITheoWindowProvider theoWindowProvider, CallbackManager callbacks) {
		this.coordProvider = coordProvider;
		this.cookieProvider = cookieProvider;
		this.kb = kb;
		this.theoWindowProvider = theoWindowProvider;
		openedWindows = new HashMap<Integer, TheoWindow>();
		this.callbacks = callbacks;
	}

	public int openWindow(DocumentInformation networkSender, Long requestWorkflowID, String title, String URL, int sizeX, int sizeY) {
		Coordinates coords = coordProvider.getRecommendedPosition();
		Cookie cookies = Cookie.newBuilder().setCookie(cookieProvider.getCookies()).setUrl(cookieProvider.getUrl()).build();
		TheoWindow wnd = theoWindowProvider.create(requestWorkflowID, sizeY, sizeX, coords.getX(), coords.getY(), title, URL, cookies, true);
		wnd.showWindow();
		openedWindows.put(wnd.getWndID(), wnd);
		return wnd.getWndID();
	}

	@Override
	public void updateWindow(DocumentInformation networkSender, int windowID, String title, String URL,
			Integer sizeX, Integer sizeY) {
		TheoWindow w = openedWindows.get(windowID);
		if (URL != null)
			w.changeURL(URL);
		Coordinates coords = coordProvider.getRecommendedPosition();
		if (sizeX != null && sizeY != null)
			w.resizeAndMove(coords.getX(), coords.getY(), sizeX, sizeY);

		w.setCookie(cookieProvider.getUrl(), cookieProvider.getCookies());
	}

	public void closeWindow(DocumentInformation networkSender, int windowID) {
		TheoWindow wnd = openedWindows.get(windowID);
		if (wnd != null) {
			wnd.closeWindow();
		}
	}

	
	public void letUserChoose(final DocumentInformation networkSender, final List<SallyMenuItem> items) {
		final Long callbackID = callbacks.registerCallback(new IMessageCallback() {

			@Override
			public void onMessage(AbstractMessage m) {
				SallyFrameChoice choice = (SallyFrameChoice) m;
				for (SallyMenuItem item : items) {
					if (item.hashCode() == choice.getChoiceId()) {
						item.run();
					}
				}
			}
		});
		
		final JFrame frame = new JFrame("Sally Services");
		final JDialog dialog = new JDialog(frame);
		dialog.setTitle("Sally Frames");
		final JPanel panel = new JPanel();
		chosenItem = null;

		panel.setLayout(new BoxLayout(panel, BoxLayout.Y_AXIS));

		ActionListener frameListener = new ActionListener() {
			/* (non-Javadoc)
			 * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
			 */
			public void actionPerformed(ActionEvent e) {
				String chosen = e.getActionCommand();
				panel.removeAll();
				dialog.setTitle("Sally Services");
				for (SallyMenuItem item : items) {
					if (item.getFrame().equals(chosen)) {
						final SallyMenuItem rr = item;
						JButton b = new JButton(item.getService());
						b.setHorizontalTextPosition(AbstractButton.CENTER);
						//b.setPreferredSize(new Dimension(100, 50));
						b.setActionCommand(item.getService());
						b.setToolTipText(item.getExplanation());
						b.addActionListener(new ActionListener() {
							public void actionPerformed(ActionEvent e) {	
								chosenItem = rr;
								new Thread(new Runnable() {
									
									@Override
									public void run() {
										kb.getProcessInstance(networkSender.getDocumentWorkflowID()).signalEvent("Message-SallyFrameChoice", SallyFrameChoice.newBuilder().setChoiceId(chosenItem.hashCode()).setCallbackToken(callbackID).setFileName("").build());									
									}
								}).start();

								dialog.dispose();
							}
						});

						panel.add(b);
					}
				}
				panel.updateUI();
				dialog.pack();
				frame.pack();
			}
		};

		frame.setDefaultCloseOperation(JFrame.HIDE_ON_CLOSE);
		Set<String> frames = new HashSet<String>();
		JLabel ll = new JLabel("Please select the frame:");
		ll.setForeground(Color.BLUE);

		panel.add(ll);
		//panel.add(new JLabel("                       "));

		for (SallyMenuItem item : items) {
			if (frames.contains(item.getFrame()))
				continue;
			frames.add(item.getFrame());
			JButton b = new JButton(item.getFrame());
			b.setHorizontalTextPosition(AbstractButton.CENTER);
			b.setPreferredSize(new Dimension(180, 25));
			b.setActionCommand(item.getFrame());
			b.addActionListener(frameListener);
			System.out.println(b.getSize().toString());
			panel.add(b);
		}

		Coordinates coords = coordProvider.getRecommendedPosition();
		dialog.setLocation(coords.getX(), coords.getY());
		dialog.setPreferredSize(new Dimension(200, 170));
		dialog.setContentPane(panel);
		dialog.pack();
		dialog.setVisible(true);
		dialog.setAlwaysOnTop(true);
	}
}
