package info.kwarc.sally.theofx;

import info.kwarc.sally.core.SallyActionAcceptor;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyService;
import info.kwarc.sally.core.comm.SallyMenuItem;

import java.awt.Dialog.ModalityType;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

import javax.swing.AbstractButton;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;

import sally.IdData;
import sally.ScreenCoordinates;
import sally.TheoChangeWindow;
import sally.TheoCloseWindow;
import sally.TheoOpenWindow;

public class TheoService {

	SallyMenuItem chosenItem;
	ScreenCoordinates coords;
	HashMap<Integer, TheoWindow> openedWindows;
	Random r = new Random();
	
	public TheoService() {
		openedWindows = new HashMap<Integer, TheoWindow>();
	}
	
	@SallyService
	public void letUserChoose(ArrayList<SallyMenuItem> items, SallyActionAcceptor acceptor, SallyContext context) {
		if (context.getContextVar("preferred_position") instanceof ScreenCoordinates) {
			coords = (ScreenCoordinates) context.getContextVar("preferred_position");
		} else {
			coords = ScreenCoordinates.newBuilder().setX(200).setY(400).build();
		}
		
		SallyMenuItem item = letUserChoose(items);
		acceptor.acceptResult(item);
	}
	
	@SallyService
	public void openWindow(TheoOpenWindow newWindow, SallyActionAcceptor acceptor, SallyContext context) {
		Integer resID = r.nextInt();
		IdData id = IdData.newBuilder().setId(resID).build();
		openedWindows.put(resID, TheoWindow.addWindow(newWindow.getSizeY(), newWindow.getSizeX(), newWindow.getPosition().getX(), newWindow.getPosition().getY(), newWindow.getTitle(), newWindow.getUrl(), newWindow.getCookie(), true));
		acceptor.acceptResult(id);
	}

	@SallyService
	public void changeWindow(TheoChangeWindow window, SallyActionAcceptor acceptor, SallyContext context) {
		if (!openedWindows.containsKey(window.getWindowid().getId())) {
			return;
		}
		TheoWindow w = openedWindows.get(window.getWindowid().getId());
		
		if (window.hasCookie()) {
			w.setCookie(window.getCookie().getUrl(), window.getCookie().getCookie());
		}
		
		if (window.hasUrl()) {
			w.changeURL(window.getUrl());
		}
	}
	
	@SallyService
	public void openWindow(TheoCloseWindow window, SallyActionAcceptor acceptor, SallyContext context) {
		Integer resID = window.getId().getId();
		TheoWindow wnd = openedWindows.get(resID);
		if (wnd != null) {
			wnd.closeWindow();
		}
	}

	public SallyMenuItem letUserChoose(final List<SallyMenuItem> items) {
		final JFrame frame = new JFrame("FrameDemo");
		final JDialog dialog = new JDialog(frame, ModalityType.APPLICATION_MODAL);
		final JPanel t = new JPanel();
		chosenItem = null;
		
		t.setLayout(new BoxLayout(t, BoxLayout.PAGE_AXIS));
		
		ActionListener frameListener = new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				String chosen = e.getActionCommand();
				t.removeAll();
				for (SallyMenuItem item : items) {
					if (item.getFrame().equals(chosen)) {
						final SallyMenuItem rr = item;
						JButton b = new JButton(item.getService());
						b.setHorizontalTextPosition(AbstractButton.CENTER);
						b.setActionCommand(item.getService());
						b.addActionListener(new ActionListener() {
							public void actionPerformed(ActionEvent e) {	
								chosenItem = rr;
								dialog.setVisible(false);
							}
						});
						t.add(b);
					}
				}
				t.updateUI();
				dialog.pack();
				frame.pack();
			}
		};
		
		frame.setDefaultCloseOperation(JFrame.HIDE_ON_CLOSE);
		Set<String> frames = new HashSet<String>();
		t.add(new JLabel("Please select the frame"));

		for (SallyMenuItem item : items) {
			if (frames.contains(item.getFrame()))
				continue;
			frames.add(item.getFrame());
			JButton b = new JButton(item.getFrame());
			b.setHorizontalTextPosition(AbstractButton.CENTER);
			b.setActionCommand(item.getFrame());
			b.addActionListener(frameListener);
			t.add(b);
		}

		dialog.setLocation(coords.getX(), coords.getY());
		dialog.setContentPane(t);
		dialog.pack();
		dialog.setVisible(true);
		frame.removeAll();
		frame.dispose();
				
		return chosenItem;
	}

}
