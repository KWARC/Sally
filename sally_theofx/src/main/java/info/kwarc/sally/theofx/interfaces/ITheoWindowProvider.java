package info.kwarc.sally.theofx.interfaces;

import info.kwarc.sally.theofx.ui.TheoWindow;
import Sally.Cookie;

import com.google.inject.assistedinject.Assisted;

public interface ITheoWindowProvider {
	TheoWindow create(@Assisted("pid") Long pid, @Assisted("sizeY") Integer sizeY, @Assisted("sizeX") Integer sizeX,
			@Assisted("posX") int posX,  @Assisted("posY") int posY, @Assisted("stageTitle") String stageTitle, @Assisted("url") String url, Cookie cookies, boolean visible);
}
