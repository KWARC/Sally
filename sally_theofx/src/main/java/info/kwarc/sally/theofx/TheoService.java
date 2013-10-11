package info.kwarc.sally.theofx;

import info.kwarc.sally.core.CookieProvider;
import info.kwarc.sally.core.ScreenCoordinatesProvider;
import info.kwarc.sally.core.comm.Coordinates;
import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.interfaces.Theo;
import info.kwarc.sally.theofx.interfaces.ITheoWindowProvider;
import info.kwarc.sally.theofx.ui.TheoWindow;
import info.kwarc.sissi.bpm.inferfaces.ISallyKnowledgeBase;

import java.awt.Color;
import java.awt.Dialog.ModalityType;
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

import sally.Cookie;

import com.google.inject.Inject;
import com.google.inject.Singleton;

@Singleton
public class TheoService implements Theo {

	SallyMenuItem chosenItem;
	HashMap<Integer, TheoWindow> openedWindows;
	ScreenCoordinatesProvider coordProvider;
	CookieProvider cookieProvider;
	ISallyKnowledgeBase kb;
	ITheoWindowProvider theoWindowProvider;

	@Inject
	public TheoService(ScreenCoordinatesProvider coordProvider, CookieProvider cookieProvider, ISallyKnowledgeBase kb, ITheoWindowProvider theoWindowProvider) {
		this.coordProvider = coordProvider;
		this.cookieProvider = cookieProvider;
		this.kb = kb;
		this.theoWindowProvider = theoWindowProvider;
		openedWindows = new HashMap<Integer, TheoWindow>();
	}

	public int openWindow(Long processInstanceID, String title, String URL, int sizeX, int sizeY) {
		Coordinates coords = coordProvider.getRecommendedPosition();
		Cookie cookies = Cookie.newBuilder().setCookie(cookieProvider.getCookies()).setUrl(cookieProvider.getUrl()).build();
		TheoWindow wnd = theoWindowProvider.create(processInstanceID, sizeY, sizeX, coords.getX(), coords.getY(), title, URL, cookies, true);
		wnd.showWindow();
		openedWindows.put(wnd.getWndID(), wnd);
		return wnd.getWndID();
	}

	@Override
	public void updateWindow(int windowID, String title, String URL,
			Integer sizeX, Integer sizeY) {
		TheoWindow w = openedWindows.get(windowID);
		if (URL != null)
			w.changeURL(URL);
		Coordinates coords = coordProvider.getRecommendedPosition();
		if (sizeX != null && sizeY != null)
			w.resizeAndMove(coords.getX(), coords.getY(), sizeX, sizeY);

		w.setCookie(cookieProvider.getUrl(), cookieProvider.getCookies());
	}

	public void closeWindow(int windowID) {
		TheoWindow wnd = openedWindows.get(windowID);
		if (wnd != null) {
			wnd.closeWindow();
		}
	}

	public SallyMenuItem letUserChoose(final List<SallyMenuItem> items) {
		final JFrame frame = new JFrame("Sally Services");
		final JDialog dialog = new JDialog(frame, ModalityType.APPLICATION_MODAL);
		dialog.setTitle("Sally Frames");
		//dialog.setLayout(new BoxLayout(dialog.getContentPane(), BoxLayout.Y_AXIS));
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
								dialog.setVisible(false);
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

		frame.removeAll();
		frame.dispose();

		return chosenItem;
	}
}
