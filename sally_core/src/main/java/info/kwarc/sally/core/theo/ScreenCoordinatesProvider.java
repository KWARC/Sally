package info.kwarc.sally.core.theo;

import info.kwarc.sally.core.interfaces.IPositionProvider;

import com.google.inject.Singleton;

@Singleton
public class ScreenCoordinatesProvider implements IPositionProvider {
	Coordinates pos;
	
	public ScreenCoordinatesProvider() {
		pos = new Coordinates(150, 150);
	}
	
	@Override
	public Coordinates getRecommendedPosition() {
		return pos;
	}

	@Override
	public void setRecommendedCoordinates(Coordinates pos) {
		this.pos = pos;
	}
}
